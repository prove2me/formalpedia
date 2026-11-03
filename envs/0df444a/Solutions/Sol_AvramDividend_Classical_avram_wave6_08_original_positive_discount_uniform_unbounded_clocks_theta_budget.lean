-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_discount_uniform_unbounded_clocks_theta_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:02:43.730868+00:00
-- url     : https://prove2.me/submissions/6fd1fa05-d322-47f9-858a-6867c2bbfec9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτmeas : Measurable (fun ω => (τ ω : ℝ))),
      ENNReal.ofReal θ *
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by
  obtain ⟨θ, hθ, hψ⟩ :=
    avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount X q hq
  refine ⟨θ, hθ, ?_⟩
  intro τ hτmeas
  exact avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
    X x C D hD θ hθ q (le_of_lt hψ) τ hτmeas
