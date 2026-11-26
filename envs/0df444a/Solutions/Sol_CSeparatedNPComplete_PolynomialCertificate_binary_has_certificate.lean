-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.binary_has_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:58.431473+00:00
-- url     : https://prove2.me/submissions/0b69e154-e329-4e64-9ff7-06b3943ca10e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (a : Vec n) (ha : is_binary a) :
    ∃ b : Fin n → Bool, selector b = a := by
  classical
  refine ⟨fun i => decide (a i = 1), ?_⟩
  funext i
  rcases ha i with hi | hi <;> simp [selector, hi]
end CSeparatedNPComplete.PolynomialCertificate
