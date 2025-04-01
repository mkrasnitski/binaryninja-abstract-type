mod derive_impl;

// Entry point to the proc-macro.
#[proc_macro_derive(AbstractType, attributes(binja))]
pub fn abstract_type_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    // Transforming the error diagnostic into tokens for emission allows the business logic to
    // return `Result` and make use of the `?` operator like any normal Rust program
    match derive_impl::impl_abstract_type(input) {
        Ok(tokens) => tokens.into(),
        Err(diag) => diag.emit_as_item_tokens().into(),
    }
}
