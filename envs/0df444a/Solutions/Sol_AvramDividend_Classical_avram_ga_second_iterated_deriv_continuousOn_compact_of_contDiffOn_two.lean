-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_second_iterated_deriv_continuousOn_compact_of_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:01:14.50108+00:00
-- url     : https://prove2.me/submissions/b4492f74-14d5-4ac4-9a3f-4b7f8c8825e9

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology Filter MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (w : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hw : ContDiffOn ℝ 2 w U)
    (a b : ℝ) (hsub : Icc a b ⊆ U) :
    ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b)  := by
  have hd : ContDiffOn ℝ 1 (deriv w) U :=
    hw.deriv_of_isOpen hU (by norm_num)
  have hc : ContinuousOn (deriv (deriv w)) U :=
    hd.continuousOn_deriv_of_isOpen hU (by norm_num)
  have heq : (fun y => iteratedDeriv 2 w y) =
      deriv (deriv w) := by
    funext y
    simp only [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
  rw [heq]
  exact hc.mono hsub
