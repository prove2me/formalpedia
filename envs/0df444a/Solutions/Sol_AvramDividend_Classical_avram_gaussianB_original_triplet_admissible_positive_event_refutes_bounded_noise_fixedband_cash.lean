-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_triplet_admissible_positive_event_refutes_bounded_noise_fixedband_cash
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:11:08.899207+00:00
-- url     : https://prove2.me/submissions/afde9755-4f75-4ca4-a306-4ab8ae59dcf5

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ), MeasurableSet E ∧
        0 < gaussianLimit E ∧
        ∀ (N : (ℝ≥0 → ℝ) → ℝ),
          (∀ᵐ ω ∂(gaussianLimit.restrict E),
            |N ω| ≤ (1 / 4000 : ℝ)) →
          ¬ (∀ᵐ ω ∂(gaussianLimit.restrict E), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) := by
  obtain ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, hEv⟩ :=
    avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  have hle : (1 / 1000 : ℝ≥0) ≤ 17 / 16000 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  refine ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, ?_⟩
  intro N hN hB
  exact avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted Y E hE hpos
    (fun ω s => brownian s ω - brownian 0 ω)
    (fun ω hω s hs => (hEv ω hω s (hs.trans hle)).1)
    (fun ω hω s hs => (hEv ω hω s (hs.trans hle)).2.1)
    N hN hB
