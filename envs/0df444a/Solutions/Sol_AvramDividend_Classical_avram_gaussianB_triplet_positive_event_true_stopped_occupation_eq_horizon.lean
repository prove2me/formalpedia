-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_triplet_positive_event_true_stopped_occupation_eq_horizon
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:19:34.719201+00:00
-- url     : https://prove2.me/submissions/72705f65-6791-40a9-b8d9-d44221581c26

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_NNReal_first_contact_floor_real_physical_times
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
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
          (∫ u in Ioo (0 : ℝ) (1 : ℝ),
            (if u < (1 / 1000 : ℝ) ∧
              (5 / 44 : ℝ) <
                riskProcess Y (1 / 8 : ℝ)
                  (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal u) ω
            then (1 : ℝ) else 0) ∂volume) =
            (1 / 1000 : ℝ) := by
  have hle : (1 / 1000 : ℝ≥0) ≤ 17 / 16000 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hpos0 : (0 : ℝ≥0) < 1 / 1000 := by norm_num
  obtain ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, hEv⟩ :=
    avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  have hTube : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) → |Y.X s ω| ≤ (1 / 400 : ℝ) :=
    fun ω hω s hs => (hEv ω hω s (hs.trans hle)).2.2
  have hle1 : (((1 / 1000 : ℝ≥0) : ℝ)) ≤ ((1 : ℕ) : ℝ) := by push_cast; norm_num
  refine ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, ?_⟩
  intro ω hω
  have h := avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
    (fun s => riskProcess Y (1 / 8 : ℝ) (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω)
    (5 / 44 : ℝ) (1 / 1000 : ℝ≥0) 1 hpos0 hle1 (by
      intro t ht0 ht1
      have hts : Real.toNNReal t ≤ (1 / 1000 : ℝ≥0) := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0.le]; exact ht1.le
      exact avram_gbB38_barrier_reserve_above_cutoff_on_tube Y (Real.toNNReal t) ω
        (fun s hs => hTube ω hω s (hs.trans hts)))
  have e1 : (((1 / 1000 : ℝ≥0) : ℝ)) = (1 / 1000 : ℝ) := by push_cast; ring
  rw [e1] at h
  simpa using h
