-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb45_open_C2_compact_hessian_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:46:44.113163+00:00
-- url     : https://prove2.me/submissions/bb71154c-03a9-4003-bd17-cfd39d28f638

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gb40_compact_hessian_absolute_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- A compact interval inside an open C2 domain has a bounded Hessian. -/
theorem solution
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) (a b : ℝ)
    (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, |iteratedDeriv 2 w y| ≤ B := by
  have hu : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hc : ContinuousOn (iteratedDerivWithin 2 w s) s :=
    hw.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn (iteratedDerivWithin 2 w s) (iteratedDeriv 2 w) s :=
    iteratedDerivWithin_of_isOpen hs
  have hc' : ContinuousOn (iteratedDeriv 2 w) (Icc a b) := by
    exact (hc.congr heq.symm).mono hsub
  exact avram_gb40_compact_hessian_absolute_bound
    w a b hab hc'.abs
