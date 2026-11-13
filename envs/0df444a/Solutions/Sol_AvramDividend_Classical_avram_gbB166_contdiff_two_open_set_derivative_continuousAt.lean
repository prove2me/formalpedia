-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB166_contdiff_two_open_set_derivative_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:07:30.728208+00:00
-- url     : https://prove2.me/submissions/37268a4f-8055-4c70-80ad-7425c794104b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hw : ContDiffOn ℝ 2 w U) (y : ℝ) (hy : y ∈ U) :
    ContinuousAt (deriv w) y := by
  have hderiv : ContinuousOn (deriv w) U :=
    hw.continuousOn_deriv_of_isOpen hU (by norm_num)
  exact hderiv.continuousAt (hU.mem_nhds hy)
