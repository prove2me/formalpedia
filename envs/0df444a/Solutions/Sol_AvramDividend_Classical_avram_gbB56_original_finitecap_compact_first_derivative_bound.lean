-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB56_original_finitecap_compact_first_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:56:02.217222+00:00
-- url     : https://prove2.me/submissions/cfa9600b-9c5a-4b2d-aca4-bf1c495566e4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb43_finitecap_compact_interior_band
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Icc (δ / 2)
        (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))),
        |deriv w y| ≤ B := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  change ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, |deriv w y| ≤ B
  obtain ⟨hopen, hsub⟩ :=
    avram_gb43_finitecap_compact_interior_band C hC hFiniteCap δ hδ j
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hopen.uniqueDiffOn
  have hc : ContinuousOn
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (iteratedDeriv 1 w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    iteratedDerivWithin_of_isOpen hopen
  have hc' : ContinuousOn (fun y => |deriv w y|) (Icc a b) := by
    simpa only [iteratedDeriv_one] using
      ((hc.congr heq.symm).mono hsub).abs
  by_cases hab : a ≤ b
  · obtain ⟨z, hz, hzmax⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc'
    refine ⟨|deriv w z|, abs_nonneg _, ?_⟩
    intro y hy
    exact hzmax hy
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    exact (hab (hy.1.trans hy.2)).elim
