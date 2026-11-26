-- Prove2me | solution 1 for ClassicalComplexWPT.seqLowShift_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:01.618924+00:00
-- url     : https://prove2.me/submissions/4435bcf9-78d7-42e6-8dc4-e172e138da39

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
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqLowShift d f n = f (n - d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : d + m - d = m := Nat.add_sub_cancel_left d m
  rw [hsub]
  simpa only [Nat.add_comm] using seqLowShift_apply_add d f m
end ClassicalComplexWPT
