-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:01:15.892527+00:00
-- url     : https://prove2.me/submissions/245f812f-edf0-4b59-bab9-cea85f4fb597

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (s t : ℝ≥0) (hst : s ≤ t)
    (hJI : Integrable (fun ω => Jsmall t ω - Jsmall s ω) P) :
    (∫ ω, ‖Jsmall t ω - Jsmall s ω‖ ∂P) ≤
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioo (-1 : ℝ) 0)).toReal +
      ((t : ℝ) - (s : ℝ)) *
        ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFiniteP : P Set.univ < ⊤ := by
    rw [measure_univ]
    exact ENNReal.one_lt_top
  letI : IsFiniteMeasure P := ⟨hFiniteP⟩
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Ioo (-1 : ℝ) 0)
  let d : ℝ := ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν
  let c : ℝ := ((t : ℝ) - (s : ℝ)) * ‖d‖
  have hBand : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hz.2
  have hCount :=
    AvramDividend.Classical.avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
      X hFinite s t hst (Ioo (-1 : ℝ) 0) measurableSet_Ioo hBand
  change Integrable (fun ω => (N ω).toReal) P ∧
    (∫ ω, (N ω).toReal ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioo (-1 : ℝ) 0)).toReal at hCount
  have hPath :=
    AvramDividend.Classical.avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
      X hFinite Jsmall hJsource t
  have hBound : ∀ᵐ ω ∂P,
      ‖Jsmall t ω - Jsmall s ω‖ ≤ (N ω).toReal + c := by
    filter_upwards [hPath] with ω hω
    simpa only [N, c, d] using hω s t hst le_rfl
  have hNormI : Integrable
      (fun ω => ‖Jsmall t ω - Jsmall s ω‖) P :=
    hJI.norm
  have hMajorI : Integrable (fun ω => (N ω).toReal + c) P :=
    hCount.1.add (integrable_const c)
  have hCmp :
      (∫ ω, ‖Jsmall t ω - Jsmall s ω‖ ∂P) ≤
      (∫ ω, (N ω).toReal + c ∂P) :=
    integral_mono_ae hNormI hMajorI hBound
  calc
    (∫ ω, ‖Jsmall t ω - Jsmall s ω‖ ∂P) ≤
      (∫ ω, (N ω).toReal + c ∂P) := hCmp
    _ = (∫ ω, (N ω).toReal ∂P) + c := by
      rw [integral_add hCount.1 (integrable_const c)]
      simp
    _ = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioo (-1 : ℝ) 0)).toReal +
        ((t : ℝ) - (s : ℝ)) *
          ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by
      rw [hCount.2]
