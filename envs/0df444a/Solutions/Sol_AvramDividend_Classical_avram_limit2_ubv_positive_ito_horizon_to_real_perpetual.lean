-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_positive_ito_horizon_to_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:19:39.067966+00:00
-- url     : https://prove2.me/submissions/6885fc88-9445-4868-8baf-3ab9bbb86b64

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_one_future_clock_uniform_cap_top
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive-horizon original UBV stopped Ito cash bounds give real
    perpetual dividend cash and all capped/top values, including time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      0 < x → ∀ (T : ℝ), 0 < T → ∀ (n : ℕ), 0 < n →
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D = ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hFuture : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < x →
        ∃ n : ℕ, T < (n : ℝ) ∧
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc D hD T hT hxpos
    obtain ⟨n, hn⟩ := exists_nat_gt T
    have hnpos : 0 < n := by
      have hreal : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hT hn
      exact_mod_cast hreal
    refine ⟨n, hn, ?_⟩
    refine le_trans ?_ (hSource x hx hxc D hD hxpos (T + 1) (by linarith) n hnpos)
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    have hStep : T ≤ T + 1 :=
      le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
    exact ⟨ht.1, le_trans ht.2 hStep⟩
  have hV := avram_limit2_ubv_one_future_clock_uniform_cap_top
    X hBV q w C hw0 hFuture
  refine ⟨?_, hV.1, hV.2⟩
  intro x hx hxc D hD
  exact avram_limit2_capped_value_bound_to_real_expected_cash
    X q x C (w x) (hw x hx hxc) (hV.1 x hx hxc) D hD
