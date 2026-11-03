-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:37:25.954582+00:00
-- url     : https://prove2.me/submissions/4459f420-27d0-4705-a760-943c9b19132a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ B : ℕ → Set ℝ,
      (∀ n, MeasurableSet (B n)) ∧
      (∀ n, (X.ν.restrict (Iio (0 : ℝ))) (B n) < ⊤) ∧
      Monotone B ∧
      (⋃ n, B n) = Set.univ := by
  classical
  let νneg : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hmin_meas :
      AEStronglyMeasurable (fun z : ℝ => min 1 (z ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun z : ℝ => min 1 (z ^ 2)) := by
    filter_upwards with z
    positivity
  have hminfull :
      Integrable (fun z : ℝ => min 1 (z ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin :
      Integrable (fun z : ℝ => min 1 (z ^ 2)) νneg :=
    hminfull.mono_measure Measure.restrict_le_self
  have hmin_meas' :
      AEStronglyMeasurable (fun z : ℝ => min 1 (z ^ 2)) νneg := by
    fun_prop
  have hmin_nonneg' :
      0 ≤ᵐ[νneg] (fun z : ℝ => min 1 (z ^ 2)) := by
    filter_upwards with z
    positivity
  have henergy : ∫⁻ z, g z ∂νneg < ∞ := by
    have hnotop : ∫⁻ z, g z ∂νneg ≠ ∞ := by
      dsimp [g]
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hmin_meas' hmin_nonneg').mpr hmin
    exact lt_top_iff_ne_top.mpr hnotop
  have hzeroMeas : MeasurableSet {z : ℝ | g z = 0} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (hg (measurableSet_singleton (0 : ℝ≥0∞)))
  have hzero : νneg {z | g z = 0} = 0 := by
    change (X.ν.restrict (Iio (0 : ℝ))) {z | g z = 0} = 0
    rw [Measure.restrict_apply hzeroMeas]
    have hEmpty : {z : ℝ | g z = 0} ∩ Iio (0 : ℝ) = ∅ := by
      ext z
      constructor
      · rintro ⟨hz, hneg⟩
        have hpos : (0 : ℝ) < min 1 (z ^ 2) :=
          lt_min (by norm_num) (sq_pos_of_neg hneg)
        have hzle : min 1 (z ^ 2) ≤ 0 := by
          change ENNReal.ofReal (min 1 (z ^ 2)) = 0 at hz
          exact ENNReal.ofReal_eq_zero.mp hz
        exact (not_le.mpr hpos) hzle
      · simp
    rw [hEmpty]
    exact measure_empty
  let B : ℕ → Set ℝ := fun n =>
    {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
  obtain ⟨hBm, hBfinite, hBmono, hBcover⟩ :=
    avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
      νneg g hg henergy hzero
  exact ⟨B, hBm, hBfinite, hBmono, hBcover⟩
