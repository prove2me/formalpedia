-- Prove2me | solution 2 for AvramDividend.Classical.avram_gaussianB_actual_triplet_joint_long_tube_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:45:49.898884+00:00
-- url     : https://prove2.me/submissions/a156b66d-39ab-434e-9611-6929b746b76b

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source
import Theorems.Thm_AvramDividend_Classical_avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Actual original HJB-admissible Gaussian triplet and positive joint tube. -/
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
      0 < gaussianLimit {ω : ℝ≥0 → ℝ |
        ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          |Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ)| < (1 / 4000 : ℝ) ∧
          |Y.X ⟨s, s.2.1⟩ ω| < (1 / 400 : ℝ)} := by
  obtain ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV⟩ :=
    avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
  obtain ⟨hAdm, _⟩ :=
    avram_gbB30_original_barrier_no_initial_atom_source
      Y (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
      (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (le_refl _)
  refine ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV, hAdm, ?_⟩
  have hPos :=
    avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
  have hSub :
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval,
        s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| < (1 / 4000 : ℝ) ∧
        |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
          2 * (s : ℝ)| < (1 / 400 : ℝ)} ⊆
      {ω : ℝ≥0 → ℝ | ∀ s : unitInterval,
        s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ)| < (1 / 4000 : ℝ) ∧
        |Y.X ⟨s, s.2.1⟩ ω| < (1 / 400 : ℝ)} := by
    intro ω hω s hs
    have h := hω s hs
    have hAt :
        Y.X ⟨s, s.2.1⟩ ω =
        brownian ⟨s, s.2.1⟩ ω - brownian 0 ω + 2 * (s : ℝ) := by
      exact hpath ⟨s, s.2.1⟩ ω
    have hEq :
        Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ) =
        brownian ⟨s, s.2.1⟩ ω - brownian 0 ω := by
      calc
        Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ) =
            (brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
              2 * (s : ℝ)) - 2 * (s : ℝ) :=
          congrArg (fun z : ℝ => z - 2 * (s : ℝ)) hAt
        _ = brownian ⟨s, s.2.1⟩ ω - brownian 0 ω := by
          ring
    constructor
    · calc
        |Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ)| =
            |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| :=
          congrArg abs hEq
        _ < (1 / 4000 : ℝ) := h.1
    · calc
        |Y.X ⟨s, s.2.1⟩ ω| =
            |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
              2 * (s : ℝ)| :=
          congrArg abs hAt
        _ < (1 / 400 : ℝ) := h.2
  exact lt_of_lt_of_le hPos (measure_mono hSub)
