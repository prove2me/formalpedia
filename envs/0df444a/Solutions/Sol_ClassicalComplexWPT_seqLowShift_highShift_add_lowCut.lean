-- Prove2me | solution 1 for ClassicalComplexWPT.seqLowShift_highShift_add_lowCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:58.583438+00:00
-- url     : https://prove2.me/submissions/b1c28fd8-880f-4828-81d8-0d1f3c22f132

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_lt
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_le
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff ℕ) :
    seqLowShift d (seqHighShift d f) + seqLowCut d f = f := by
  apply lp.ext
  funext n
  by_cases hn : n < d
  · simp [seqLowShift_apply_of_lt d _ hn, seqLowCut_apply_of_lt d _ hn]
  · change seqLowShift d (seqHighShift d f) n + seqLowCut d f n = f n
    rw [seqLowCut_apply_of_le d f (Nat.le_of_not_gt hn), add_zero]
    rw [seqLowShift_apply_of_le d _ (Nat.le_of_not_gt hn)]
    simp [Nat.sub_add_cancel (Nat.le_of_not_gt hn)]
end ClassicalComplexWPT
