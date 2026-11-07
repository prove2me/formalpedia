-- Prove2me | solution 5 for AvramDividend.Classical.avram_p3_bv_original_source_signed_fatou_grid_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:16:41.430776+00:00
-- url     : https://prove2.me/submissions/bca5ba2b-0e0a-408d-9970-31c6c396f7f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original BV certificate case split. The positive and zero benchmark
branches both reduce to one unchanged original stopped physical-grid source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases hwpos : 0 < w x
  · exact avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc hwpos D hD hw_nonneg hjump T hT hTpos
  · have hEnv := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad x hx hxc
        x (by exact ⟨hx, le_rfl⟩)
    have hwzero : w x = 0 := by
      have hNonneg : 0 ≤ w x := by linarith
      exact le_antisymm (le_of_not_gt hwpos) hNonneg
    have hPayoffZero :=
      avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc hwzero D hD hw_nonneg hjump T hT hTpos
    refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact measurable_const
    · intro n
      exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall (fun _ => le_refl 0)
    · intro n
      constructor
      · exact integrable_const _
      · simp
    · intro n
      exact Filter.Eventually.of_forall (fun _ => by simp [hwzero])
    · filter_upwards [hPayoffZero] with ω hω
      simp [hω]
