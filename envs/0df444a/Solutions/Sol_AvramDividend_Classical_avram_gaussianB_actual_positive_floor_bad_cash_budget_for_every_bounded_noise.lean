-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_actual_positive_floor_bad_cash_budget_for_every_bounded_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:10:31.671287+00:00
-- url     : https://prove2.me/submissions/bbc003e1-ad34-48a7-a392-90d06e2798d5

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original positive floor clock together with source-faithful fixed-band cash contradiction. -/
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
        (∀ ω ∈ E, sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
              Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) = (1 / 1000 : ℝ≥0)) ∧
        ∀ (N : (ℝ≥0 → ℝ) → ℝ),
          (∀ᵐ ω ∂(gaussianLimit.restrict E),
            |N ω| ≤ (1 / 4000 : ℝ)) →
          ¬ (∀ᵐ ω ∂(gaussianLimit.restrict E), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, hGeom⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
      (1 / 1000 : ℝ≥0) (by norm_num)
  obtain ⟨E, hMeas, hPos, hTube⟩ :=
    avram_gaussianB_canonical_measurable_positive_joint_long_tube
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
  have hDrift : ∀ ω ∈ E, ∀ t : ℝ≥0,
      t ≤ (1 / 1000 : ℝ≥0) →
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by
    intro ω hω t ht
    have hBound :=
      avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
        (fun u => |brownian u ω - brownian 0 ω + 2 * (u : ℝ)|)
        (1 / 400 : ℝ) (by
          intro u hu
          exact (hTube ω hω u hu).2) t ht
    exact (congrArg abs (hpath t ω)).trans_le hBound
  refine ⟨𝓕, Y, hStand, hUBV, hAdm, E, hMeas, hPos, ?_, ?_⟩
  · intro ω hω
    exact (hGeom ω (hDrift ω hω)).1
  · intro N hNoise hBudget
    exact avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
      Y E hMeas hPos
      (fun ω t => brownian t ω - brownian 0 ω)
      hSource hCentered N hNoise hBudget
