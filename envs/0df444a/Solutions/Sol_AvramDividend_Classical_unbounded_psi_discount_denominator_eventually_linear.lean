-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_psi_discount_denominator_eventually_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:57:03.538748+00:00
-- url     : https://prove2.me/submissions/3937d854-5a00-4dde-808f-d81062181d1b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_of_unbounded_variation
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C * θ + q < X.ψ θ := by
  intro C
  obtain ⟨β, hβ1, hβ⟩ :=
    AvramDividend.Classical.psi_normalised_unbounded_of_unbounded_variation X hnbv (C + 1)
  refine ⟨max β (max q 1), le_max_of_le_left hβ1, fun θ hθ => ?_⟩
  have hθβ : β ≤ θ := le_trans (le_max_left _ _) hθ
  have hθq : q ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ
  have hθpos : 0 < θ := lt_of_lt_of_le one_pos (le_trans hβ1 hθβ)
  have h := hβ θ hθβ
  rw [lt_div_iff₀ hθpos] at h
  nlinarith
