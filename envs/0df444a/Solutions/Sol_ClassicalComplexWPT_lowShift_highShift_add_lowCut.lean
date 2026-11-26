-- Prove2me | solution 1 for ClassicalComplexWPT.lowShift_highShift_add_lowCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:56.295073+00:00
-- url     : https://prove2.me/submissions/8e453ff4-cc4d-45b7-af77-a394796a447f

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_lowShift_apply_of_lt
import Theorems.Thm_ClassicalComplexWPT_lowShift_apply_of_le
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff (A × ℕ)) :
    lowShift d (highShift d f) + lowCut d f = f := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  by_cases hn : n < d
  · simp [lowShift_apply_of_lt d _ _ hn, lowCut_apply_of_lt d _ _ hn]
  · change lowShift d (highShift d f) (a,n) + lowCut d f (a,n) = f (a,n)
    rw [lowCut_apply_of_le d f a (Nat.le_of_not_gt hn), add_zero]
    rw [lowShift_apply_of_le d _ a (Nat.le_of_not_gt hn)]
    simp [Nat.sub_add_cancel (Nat.le_of_not_gt hn)]
end ClassicalComplexWPT
