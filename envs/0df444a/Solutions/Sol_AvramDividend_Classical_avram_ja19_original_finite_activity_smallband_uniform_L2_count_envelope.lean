-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:03:07.34455+00:00
-- url     : https://prove2.me/submissions/40f56c81-d608-451a-b164-2231dab05dbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ja19_integrable_square_add_of_L2_components
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by
  intro T
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let C : ℝ := (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal
  let B : Ω → ℝ := fun ω => (N ω).toReal + C
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P :=
    (avram_anoise18_original_total_negative_count_finite_activity_L2
      X hFinite T).1
  have hNmeas : AEStronglyMeasurable (fun ω => (N ω).toReal) P := by
    have hs : AEStronglyMeasurable
        (fun ω => Real.sqrt ((N ω).toReal ^ 2)) P :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hN2.aestronglyMeasurable
    convert hs using 1
    funext ω
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)]
  have hCmeas : AEStronglyMeasurable (fun _ : Ω => C) P :=
    stronglyMeasurable_const.aestronglyMeasurable
  have hC2 : Integrable (fun _ : Ω => C ^ 2) P := integrable_const _
  have hB2 : Integrable (fun ω => (B ω) ^ 2) P :=
    avram_ja19_integrable_square_add_of_L2_components
      (fun ω => (N ω).toReal) (fun _ => C)
      hNmeas hCmeas hN2 hC2
  refine ⟨B, hB2, ?_⟩
  simpa only [B, C, N] using
    avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
      X hFinite T
