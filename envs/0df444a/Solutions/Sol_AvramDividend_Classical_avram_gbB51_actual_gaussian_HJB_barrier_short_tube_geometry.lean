-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:55:41.281592+00:00
-- url     : https://prove2.me/submissions/4c7ca2b1-a002-4325-abcb-38ce360b2d0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original HJB-admissible native Gaussian witness with exact tube geometry. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ T → |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        sInf ((Icc (0 : ℝ≥0) T ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
            Ici (-(5 / 44 : ℝ))) ∪ {T}) = T ∧
        (5 / 44 : ℝ) <
          riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ∧
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
          (1 / 8 : ℝ)) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, h0, hcont, hneg, hC2, hGen,
      hAdm⟩ :=
    avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, ?_⟩
  intro ω hTube
  exact ⟨
    avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
      Y T ω hTube,
    avram_gbB38_barrier_reserve_above_cutoff_on_tube
      Y T ω hTube,
    avram_gbB49_original_short_barrier_terminal_reserve_le_cap
      Y T ω hT hTube⟩
