-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_psi_discount_reciprocal_small
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:00:13.844139+00:00
-- url     : https://prove2.me/submissions/1ab4d04d-3de0-4643-a6a1-00b5ea1e2b3d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ β : ℝ, 1 ≤ β ∧
        ∀ θ : ℝ, β ≤ θ →
          0 ≤ θ / (X.ψ θ - q) ∧
            θ / (X.ψ θ - q) < ε := by
  intro ε hε
  obtain ⟨β, hβ1, hβ⟩ :=
    AvramDividend.Classical.unbounded_psi_discount_denominator_eventually_linear X hnbv q hq (1 / ε)
  refine ⟨β, hβ1, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := by linarith
  have h := hβ θ hθ
  have hpos : 0 < 1 / ε * θ := by positivity
  have hd : 0 < X.ψ θ - q := by linarith
  refine ⟨div_nonneg hθ0.le hd.le, ?_⟩
  rw [div_lt_iff₀ hd]
  have : θ = ε * (1 / ε * θ) := by field_simp
  nlinarith
