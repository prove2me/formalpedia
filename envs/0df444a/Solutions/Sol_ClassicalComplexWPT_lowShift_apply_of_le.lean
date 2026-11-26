-- Prove2me | solution 1 for ClassicalComplexWPT.lowShift_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:18.048865+00:00
-- url     : https://prove2.me/submissions/89cf3a7e-037b-4921-b9f6-de6556d32ce6

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : d ≤ n) : lowShift d f (a,n) = f (a, n - d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : d + m - d = m := Nat.add_sub_cancel_left d m
  rw [hsub]
  simpa only [Nat.add_comm] using lowShift_apply_add d f a m
end ClassicalComplexWPT
