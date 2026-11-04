-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_compact_physical_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:10:05.546276+00:00
-- url     : https://prove2.me/submissions/a361d71b-9389-44ee-a089-3a22b911968f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) (-ε)) X.ν ∧
    ∃ B : ℝ, ∀ y ∈ Icc u v,
      |(X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) * deriv w y| ≤ B := by
  have hmark : IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) (-ε)) X.ν :=
    avram_p4_c_generator_cutoff_linear_mark_integrable X ε hε
  have hdc : ContinuousOn (deriv w) (Ioo 0 C) :=
    hw.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsub : Icc u v ⊆ Ioo 0 C := by
    intro y hy
    exact ⟨lt_of_lt_of_le hu hy.1, lt_of_le_of_lt hy.2 hv⟩
  have hcompact : IsCompact (Icc u v) := isCompact_Icc
  have hcont : ContinuousOn (deriv w) (Icc u v) := hdc.mono hsub
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨hmark, ⟨|X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν| * |M|, ?_⟩⟩
  intro y hy
  have hderiv : |deriv w y| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM y hy
  calc
    |(X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) * deriv w y| =
        |X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν| * |deriv w y| := abs_mul _ _
    _ ≤ |X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν| * |M| :=
        mul_le_mul_of_nonneg_left (hderiv.trans (le_abs_self M)) (abs_nonneg _)
