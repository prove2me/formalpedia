-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.run_work_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:20.797596+00:00
-- url     : https://prove2.me/submissions/be30b373-7709-4ce6-847a-7cad2622085b

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_mass_le

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (xs : List (ℕ × Bool)) :
    (run xs).work ≤ 16 * xs.length * (budget xs + 1) := by
  induction xs with
  | nil => simp [run]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    have hm := run_mass_le xs
    cases b <;>
      simp only [run, Bool.false_eq_true, ↓reduceIte, binaryCost, Nat.size_one,
        List.length_cons, budget, List.map_cons, List.sum_cons, bitMass] at * <;> nlinarith
end CSeparatedNPComplete.PolynomialCertificate
