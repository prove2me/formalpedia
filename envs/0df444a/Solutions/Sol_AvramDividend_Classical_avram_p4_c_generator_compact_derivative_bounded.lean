-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_compact_derivative_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:02:03.05848+00:00
-- url     : https://prove2.me/submissions/a4e489aa-fd30-44df-a49b-5318150e9abf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (w : ℝ → ℝ) (C u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) :
    ∃ M : ℝ, ∀ y ∈ Icc u v, |deriv w y| ≤ M := by
  have hdc : ContinuousOn (deriv w) (Ioo 0 C) :=
    hw.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsub : Icc u v ⊆ Ioo 0 C := by
    intro y hy
    exact ⟨lt_of_lt_of_le hu hy.1, lt_of_le_of_lt hy.2 hv⟩
  have hcompact : IsCompact (Icc u v) := isCompact_Icc
  have hcont : ContinuousOn (deriv w) (Icc u v) := hdc.mono hsub
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨M, ?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using hM y hy
