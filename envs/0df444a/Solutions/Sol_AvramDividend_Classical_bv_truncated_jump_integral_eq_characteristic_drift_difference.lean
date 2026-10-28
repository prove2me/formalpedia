-- Prove2me | solution 1 for AvramDividend.Classical.bv_truncated_jump_integral_eq_characteristic_drift_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:07:48.118246+00:00
-- url     : https://prove2.me/submissions/75e18d43-d6fd-41a2-bed1-34bf7804bd52

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_drift_compensation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Truncated negative-jump compensation is precisely c minus physical drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    (∫ y in Iio (0 : ℝ),
      y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) =
    X.c - X.drift := by
  have hmean :
      (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) = X.c - X.drift := by
    have h := boundedVariation_drift_compensation_identity
      X hBV (fun z : ℝ => z) (0 : ℝ)
    have hd : deriv (fun z : ℝ => z) (0 : ℝ) = 1 := by simp
    rw [hd] at h
    simp only [one_mul] at h
    linarith
  have hind :
      (∫ y in Iio (0 : ℝ),
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) =
      (∫ y in Iio (0 : ℝ),
        (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) y ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    by_cases h : -1 < y
    · have hmem1 : y ∈ Ioo (-1 : ℝ) 1 := ⟨h, lt_trans hy (by norm_num)⟩
      have hmem0 : y ∈ Ioo (-1 : ℝ) 0 := ⟨h, hy⟩
      simp [hmem1, hmem0]
    · have hnot1 : y ∉ Ioo (-1 : ℝ) 1 := fun hmem => h hmem.1
      have hnot0 : y ∉ Ioo (-1 : ℝ) 0 := fun hmem => h hmem.1
      simp [hnot1, hnot0]
  rw [hind]
  rw [integral_indicator measurableSet_Ioo]
  have hsub : Ioo (-1 : ℝ) 0 ∩ Iio (0 : ℝ) = Ioo (-1 : ℝ) 0 := by
    ext y
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, hy.2⟩
  rw [Measure.restrict_restrict measurableSet_Ioo, hsub]
  exact hmean
