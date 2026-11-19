-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_triplet_positive_event_terminal_HJB_surplus_and_cap_defect
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:12:40.033515+00:00
-- url     : https://prove2.me/submissions/e53f85a1-fdc4-4fa6-8fa0-24a9e4fca3f7

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB34_sigma1_upper_band_positive_drift
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
        ∀ ω ∈ E,
          (193419 / 96800 : ℝ) ≤
             2 - (1 / 100 : ℝ) * ((riskProcess Y (1 / 8 : ℝ)
              (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
              (1 / 1000 : ℝ≥0) ω) + 15 / 242) ∧
          0 ≤ (riskProcess Y (1 / 8 : ℝ)
              (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
              (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess Y (1 / 8 : ℝ)
              (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
              (1 / 1000 : ℝ≥0) ω) ^ 2 - 15 / 242 ∧
          (riskProcess Y (1 / 8 : ℝ)
              (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
              (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess Y (1 / 8 : ℝ)
              (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
              (1 / 1000 : ℝ≥0) ω) ^ 2 - 15 / 242 ≤
             (1 / 1936 : ℝ) := by
  have hle : (1 / 1000 : ℝ≥0) ≤ 17 / 16000 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hpos0 : (0 : ℝ≥0) < 1 / 1000 := by norm_num
  obtain ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, hEv⟩ :=
    avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  have hTube : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) → |Y.X s ω| ≤ (1 / 400 : ℝ) :=
    fun ω hω s hs => (hEv ω hω s (hs.trans hle)).2.2
  refine ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, ?_⟩
  intro ω hω
  exact avram_gbB34_sigma1_upper_band_positive_drift _
    (avram_gbB38_barrier_reserve_above_cutoff_on_tube Y _ ω (hTube ω hω)).le
    (avram_gbB49_original_short_barrier_terminal_reserve_le_cap Y _ ω hpos0 (hTube ω hω))
