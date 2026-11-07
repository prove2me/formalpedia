-- Prove2me | solution 7 for AvramDividend.Classical.avram_p3_bv_original_source_signed_fatou_grid_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:29:25.512432+00:00
-- url     : https://prove2.me/submissions/f4e790ba-2b72-4bc8-9eea-e0e32e655d91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
-- These two source-exact children are currently OPEN; do not lint-submit this
-- staged canonical solution until both have authoritative Proved status.
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Staged exact canonical closure from the two genuine source-backed
positive/zero benchmark children. This is NOT yet a compiled submission. -/
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
  have hwbound : x ≤ w x :=
    (avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
      X C hC w hw_cont hw0 hw_smooth hw_grad x hxc D hD).2
  have hwxnonneg : 0 ≤ w x := le_trans hx hwbound
  by_cases hwpos : 0 < w x
  · exact avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc hwpos D hD hw_nonneg hjump T hT hTpos
  · have hwzero : w x = 0 :=
      le_antisymm (le_of_not_gt hwpos) hwxnonneg
    have hPayzero :=
      avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc hwzero D hD hw_nonneg hjump T hT hTpos
    refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact measurable_const
    · intro n
      simp
    · intro n
      filter_upwards [] with ω
      simp
    · intro n
      simp
    · intro n
      filter_upwards [] with ω
      simp [hwzero]
    · filter_upwards [hPayzero] with ω hp
      dsimp at hp ⊢
      rw [hp]
      simp
