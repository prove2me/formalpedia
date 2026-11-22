-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_ubv_original_canonical_ito_integral_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:39:09.925685+00:00
-- url     : https://prove2.me/submissions/7dedeb58-75d9-4667-a193-a4815f7927fc

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_original_affine_brownian_source
import Theorems.Thm_AvramDividend_Classical_avram_lsc_original_gaussian_unit_window_complete
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal
noncomputable section

/-- Original zero-jump unbounded variation supplies its own Brownian
driver and a full, witness-bearing canonical Itô representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (ℱr : Filtration ℝ mΩ)
        (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱr)
        (b : ℝ) (hb : 0 < b),
      ∃ (hm : Measurable (Function.uncurry
          (fun ω s => (stepIoc₀ Ω hb).eval s ω)))
        (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱr
          (fun ω s => (stepIoc₀ Ω hb).eval s ω))
        (hq : ∀ T, 0 < T →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖(stepIoc₀ Ω hb).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱr hℱ
        (fun ω s => (stepIoc₀ Ω hb).eval s ω)
        hm hp hq b
        =ᵐ[P] fun ω =>
          (X.X (Real.toNNReal b) ω -
            (Real.toNNReal b : ℝ) * X.c) / X.σ := by
  obtain ⟨W, hAff⟩ :=
    avram_lsc_zerojump_ubv_original_affine_brownian_source X hBV hν
  have hσ : X.σ ≠ 0 :=
    ne_of_gt (avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν)
  have hW : ∀ (t : ℝ) (ω : Ω),
      W.W t ω =
        (X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.c) / X.σ := by
    intro t ω
    apply (eq_div_iff hσ).2
    have hA := hAff t ω
    linear_combination -hA
  refine ⟨W, ?_⟩
  intro ℱr hℱ b hb
  exact avram_lsc_original_gaussian_unit_window_complete
    X W ℱr hℱ hW hb

