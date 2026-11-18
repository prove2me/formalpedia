-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_positive_event_all_bounded_noise_budget_refuted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:02:15.915088+00:00
-- url     : https://prove2.me/submissions/2389ecbd-3c92-4801-99b4-ebf326a9ace4

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Concrete original Gaussian positive event defeats every bounded-noise fixed-band cash budget. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ (N : (ℝ≥0 → ℝ) → ℝ),
          (∀ᵐ ω ∂(gaussianLimit.restrict E),
            |N ω| ≤ (1 / 4000 : ℝ)) →
          ¬ (∀ᵐ ω ∂(gaussianLimit.restrict E), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) := by
  obtain ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV, hAdm,
    E, hMeas, hPos, hTube⟩ :=
    avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
  refine ⟨𝓕, Y, hStand, hUBV, hAdm,
    E, hMeas, hPos, ?_⟩
  intro N hNoise hBudget
  have hSource : ∀ ω ∈ E, ∀ t : ℝ≥0,
      t ≤ (1 / 1000 : ℝ≥0) →
      Y.X t ω = (brownian t ω - brownian 0 ω) + 2 * (t : ℝ) := by
    intro ω hω t ht
    exact hpath t ω
  have hCentered : ∀ ω ∈ E, ∀ t : ℝ≥0,
      t ≤ (1 / 1000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) := by
    intro ω hω t ht
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
      (fun u => |brownian u ω - brownian 0 ω|)
      (1 / 4000 : ℝ) (by
        intro u hu
        exact (hTube ω hω u hu).1) t ht
  exact avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
    Y E hMeas hPos (fun ω t => brownian t ω - brownian 0 ω)
    hSource hCentered N hNoise hBudget
