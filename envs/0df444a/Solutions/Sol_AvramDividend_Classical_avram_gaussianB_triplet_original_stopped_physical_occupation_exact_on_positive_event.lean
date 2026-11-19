-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_triplet_original_stopped_physical_occupation_exact_on_positive_event
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:33:54.137143+00:00
-- url     : https://prove2.me/submissions/02062552-b480-47eb-96a5-f0aa916c61c5

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_short_source_tube_of_native_joint_long_event
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
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
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
  obtain ⟨𝓕, Y, hYX, hc, hσ, hν, hS, hBV, hAdm, -⟩ :=
    avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
      (1 / 1000 : ℝ≥0) hpos0
  obtain ⟨E, hE, hpos, hEv⟩ := avram_gaussianB_canonical_measurable_positive_joint_long_tube
  have hTube : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) → |Y.X s ω| ≤ (1 / 400 : ℝ) := by
    intro ω hω s hs
    have hs' : (s : ℝ) ≤ 17 / 16000 := by
      have := NNReal.coe_le_coe.mpr (hs.trans hle); push_cast at this; linarith
    have hs1 : (s : ℝ) ≤ 1 := by linarith
    have h := (hEv ω hω ⟨(s : ℝ), s.2, hs1⟩ (by
      show ((s : ℝ)) ≤ (17 / 16000 : ℝ)
      exact hs')).2
    rw [hYX]
    exact h
  have hle1 : (((1 / 1000 : ℝ≥0) : ℝ)) ≤ ((1 : ℕ) : ℝ) := by push_cast; norm_num
  refine ⟨𝓕, Y, hYX, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, ?_⟩
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
