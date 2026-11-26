-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.selector_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:37.178534+00:00
-- url     : https://prove2.me/submissions/6c3e8ab7-7693-4511-9457-0cce981b047e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (b : Fin n → Bool) : is_binary (selector b) := by
  intro i
  cases h : b i <;> simp [selector, h]
end CSeparatedNPComplete.PolynomialCertificate
