-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.selector_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:47.778826+00:00
-- url     : https://prove2.me/submissions/c7aa7024-90e7-48f2-ac4e-951f4de51ad0

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    dot (selector b) (fun i => (s i : ℝ)) = (leftSum (tagged s b) : ℝ) := by
  simp only [dot, selector, leftSum, tagged, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : b i <;> simp [h]
end CSeparatedNPComplete.PolynomialCertificate
