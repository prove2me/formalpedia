-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.run_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:33.015971+00:00
-- url     : https://prove2.me/submissions/b6acc2f8-0836-41bf-9e14-ad9c7d27ab1e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_size_add_le

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (xs : List (ℕ × Bool)) : bitMass (run xs) ≤ budget xs := by
  induction xs with
  | nil => simp [run, bitMass, budget]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    have hlc := size_add_le (run xs).leftCount 1
    have hrc := size_add_le (run xs).rightCount 1
    have hls := size_add_le (run xs).leftSum w
    have hrs := size_add_le (run xs).rightSum w
    simp only [Nat.size_one] at hlc hrc
    cases b <;> simp only [run, Bool.false_eq_true, ↓reduceIte, bitMass,
      budget, List.map_cons, List.sum_cons] at * <;> omega
end CSeparatedNPComplete.PolynomialCertificate
