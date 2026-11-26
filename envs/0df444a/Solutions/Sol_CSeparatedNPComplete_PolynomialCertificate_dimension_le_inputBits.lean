-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.dimension_le_inputBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:50:24.872859+00:00
-- url     : https://prove2.me/submissions/dea2ea00-2998-4dde-bfb3-73b7ff9e97b3

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) : n ≤ inputBits s := by
  have h : n ≤ ∑ i, (Nat.size (s i) + 1) := by
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by omega
  unfold inputBits
  omega
end CSeparatedNPComplete.PolynomialCertificate
