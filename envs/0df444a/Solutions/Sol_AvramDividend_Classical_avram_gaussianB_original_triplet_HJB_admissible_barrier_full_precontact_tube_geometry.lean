-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:26:03.079574+00:00
-- url     : https://prove2.me/submissions/c35028ad-9128-47f4-9a8e-475cdf553f11

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Exact triplet and the complete original Gaussian barrier tube geometry. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
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
  obtain ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV⟩ :=
    avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
  obtain ⟨hAdm, _⟩ :=
    avram_gbB30_original_barrier_no_initial_atom_source
      Y (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
      (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (le_refl _)
  refine ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV, hAdm, ?_⟩
  intro ω hTube
  exact ⟨
    avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
      Y T ω hTube,
    avram_gbB38_barrier_reserve_above_cutoff_on_tube
      Y T ω hTube,
    avram_gbB49_original_short_barrier_terminal_reserve_le_cap
      Y T ω hT hTube⟩
