-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_smallband_uniform_quadratic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:08:33.029391+00:00
-- url     : https://prove2.me/submissions/d63cf4f0-61f5-47a0-9a18-67ec76e9b195

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Square-integrable original physical count dominates all finite small bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro T
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let R : ℝ := (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal
  let B : Ω → ℝ := fun ω =>
    Real.sqrt (2 * (N ω).toReal ^ 2 + 2 * R ^ 2)
  have hNsq : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFinite T).1
  have hBsquare (ω : Ω) :
      (B ω) ^ 2 = 2 * (N ω).toReal ^ 2 + 2 * R ^ 2 := by
    dsimp [B]
    rw [Real.sq_sqrt]
    positivity
  have hBint : Integrable (fun ω => (B ω) ^ 2) P := by
    have hsum : Integrable
        (fun ω => 2 * (N ω).toReal ^ 2 + 2 * R ^ 2) P :=
      (hNsq.const_mul 2).add (integrable_const _)
    convert hsum using 1
    funext ω
    exact hBsquare ω
  refine ⟨B, hBint, ?_⟩
  filter_upwards
    [avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
      X hFinite T] with ω hbound
  intro k t ht
  have hsmall :
      ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤
        (N ω).toReal + R := by
    simpa only [N, R] using hbound k t ht
  have hBnn : 0 ≤ B ω := Real.sqrt_nonneg _
  have hNRnn : 0 ≤ (N ω).toReal + R := by
    dsimp [R]
    positivity
  have hsq : ((N ω).toReal + R) ^ 2 ≤ (B ω) ^ 2 := by
    rw [hBsquare]
    nlinarith [sq_nonneg ((N ω).toReal - R)]
  nlinarith
