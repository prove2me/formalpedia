-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.selector_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:37.747488+00:00
-- url     : https://prove2.me/submissions/dc12bba3-1516-433f-a36a-12bf2fe32589

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
    dot (selector b) 1 = (leftCount (tagged s b) : ℝ) := by
  simp only [dot, selector, Pi.one_apply, mul_one, leftCount, tagged,
    List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : b i <;> simp [h]
end CSeparatedNPComplete.PolynomialCertificate
