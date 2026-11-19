-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_triplet_positive_event_true_max_drift_precontact_occupation_charge
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:12:41.792703+00:00
-- url     : https://prove2.me/submissions/6ce818d3-53fb-494a-a21d-25671e810a30

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
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
          0 < max Y.c 0 *
            (∫ t in Ioo (0 : ℝ) (1 / 1000 : ℝ),
              (if (5 / 44 : ℝ) <
                riskProcess Y (1 / 8 : ℝ)
                  (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
                then (1 : ℝ) else 0) ∂volume) := by
  have hle : (1 / 1000 : ℝ≥0) ≤ 17 / 16000 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hpos0 : (0 : ℝ≥0) < 1 / 1000 := by norm_num
  obtain ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, hEv⟩ :=
    avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  have hTube : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) → |Y.X s ω| ≤ (1 / 400 : ℝ) :=
    fun ω hω s hs => (hEv ω hω s (hs.trans hle)).2.2
  refine ⟨𝓕, Y, hc, hσ, hν, hS, hBV, hAdm, E, hE, hpos, ?_⟩
  intro ω hω
  have hI : (∫ t in Ioo (0 : ℝ) (1 / 1000 : ℝ),
      (if (5 / 44 : ℝ) <
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
          (Real.toNNReal t) ω
        then (1 : ℝ) else 0) ∂volume) = ∫ t in Ioo (0 : ℝ) (1 / 1000 : ℝ), (1 : ℝ) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hts : Real.toNNReal t ≤ (1 / 1000 : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1.le]; push_cast; exact ht.2.le
    have := avram_gbB38_barrier_reserve_above_cutoff_on_tube Y (Real.toNNReal t) ω
      (fun s hs => hTube ω hω s (hs.trans hts))
    show (if _ then _ else _) = _
    rw [if_pos this]
  rw [hI, hc]
  simp [Measure.real, Real.volume_Ioo]
