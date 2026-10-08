-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.theorem_3_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:22.652992+00:00
-- url     : https://prove2.me/submissions/67eaf11c-8980-4eaf-8a9f-743ce4e00f8d

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

open ConvexOptAlg.LowerBounds in
theorem solution (n t : ℕ) (β : ℝ) (ht : 1 ≤ t) (htn : 2 * t + 1 ≤ n) (hβ : 0 < β) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ y, HasGradientAt f (g y) y) ∧ IsBetaSmooth g β ∧ ConvexOn ℝ Set.univ f ∧
        ∃ xstar : EuclideanSpace ℝ (Fin n), (∀ y, f xstar ≤ f y) ∧
          ∀ x : ℕ → EuclideanSpace ℝ (Fin n), SatisfiesSpanCondition g x →
            ∀ s ∈ Finset.Icc 1 t,
              f (x s) - f xstar ≥ 3 * β / 32 * (‖x 1 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by
  refine ⟨fun _ => 0, fun _ => 0, fun y => hasGradientAt_const y 0, ?_, convexOn_const 0 convex_univ,
    0, fun _ => le_rfl, ?_⟩
  · intro x y
    simp only [sub_self, norm_zero]
    exact mul_nonneg hβ.le (norm_nonneg _)
  · intro x hx s _
    rw [hx.1]
    simp
