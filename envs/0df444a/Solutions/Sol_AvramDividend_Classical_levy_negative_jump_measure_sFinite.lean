-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_jump_measure_sFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:47:14.216641+00:00
-- url     : https://prove2.me/submissions/ef200756-fd08-4afd-9adf-498673fc3b34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_sFinite_of_positive_lintegrable_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SFinite (X.ν.restrict (Iio 0)) := by
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  let f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (min 1 (y ^ 2))
  have hf : AEMeasurable f μ := by
    dsimp [f]
    fun_prop
  have hpos : ∀ᵐ y ∂μ, f y ≠ 0 := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    have hsq : 0 < y ^ 2 := sq_pos_of_neg hy
    have hp : (0 : ℝ) < min 1 (y ^ 2) :=
      lt_min (by norm_num) hsq
    have hyne : y ≠ 0 := ne_of_lt hy
    dsimp [f]
    simp [ENNReal.ofReal_eq_zero, hyne]
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hminfull :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) μ :=
    hminfull.mono_measure Measure.restrict_le_self
  have hmin_meas' :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) μ := by
    fun_prop
  have hmin_nonneg' :
      0 ≤ᵐ[μ] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hint : ∫⁻ y, f y ∂μ ≠ ∞ := by
    dsimp [f]
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas' hmin_nonneg').mpr hmin
  exact sFinite_of_positive_lintegrable_density μ f hf hpos hint
