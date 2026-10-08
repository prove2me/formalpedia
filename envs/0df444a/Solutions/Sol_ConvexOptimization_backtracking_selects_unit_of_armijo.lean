-- Prove2me | solution 1 for ConvexOptimization.backtracking_selects_unit_of_armijo
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T08:30:35.338617+00:00
-- url     : https://prove2.me/submissions/b82a7a4f-95eb-420f-a56a-707a94483156

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

private theorem convexOn_univ_of_first_order {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfirst : ∀ u v, f u + ⟪g u, v - u⟫ ≤ f v) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := hfirst z x
  have hy := hfirst z y
  have hax := mul_le_mul_of_nonneg_left hx ha
  have hby := mul_le_mul_of_nonneg_left hy hb
  have hcancel :
      a * ⟪g z, x - z⟫ + b * ⟪g z, y - z⟫ = 0 := by
    have hb' : b = 1 - a := by linarith
    dsimp [z]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [hb']
    ring
  change f z ≤ a * f x + b * f y
  calc
    f z = (a + b) * f z +
        (a * ⟪g z, x - z⟫ + b * ⟪g z, y - z⟫) := by rw [hab, hcancel]; ring
    _ = a * (f z + ⟪g z, x - z⟫) +
        b * (f z + ⟪g z, y - z⟫) := by ring
    _ ≤ a * f x + b * f y := add_le_add hax hby

/-- If the unit step satisfies Armijo for a convex objective, backtracking selects it. -/
private theorem backtracking_eq_one_of_convexOn_unit_armijo {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hconv : ConvexOn ℝ Set.univ f)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht : IsBacktrackingStep f g α β x Δ t)
    (hunit : f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫) :
    t = 1 := by
  rcases hconv with ⟨_, hconv⟩
  rcases ht with ⟨⟨j, hj⟩, _, htmax⟩
  rcases htmax with rfl | hfail
  · rfl
  · cases j with
    | zero =>
        simp only [pow_zero] at hj
        exact hj
    | succ j =>
        have hβne : β ≠ 0 := ne_of_gt hβ0
        have hquot : t / β = β ^ j := by
          rw [hj, pow_succ]
          exact mul_div_cancel_right₀ _ hβne
        have hs0 : 0 ≤ t / β := by
          rw [hquot]
          positivity
        have hs1 : t / β ≤ 1 := by
          rw [hquot]
          exact pow_le_one₀ (le_of_lt hβ0) (le_of_lt hβ1)
        exfalso
        apply hfail
        calc
          f (x + (t / β) • Δ) =
              f ((1 - t / β) • x + (t / β) • (x + Δ)) := by
                congr 1
                module
          _ ≤ (1 - t / β) • f x + (t / β) • f (x + Δ) :=
            hconv (x := x) (y := x + Δ) (a := 1 - t / β) (b := t / β)
              (by simp) (by simp) (by linarith) hs0 (by ring)
          _ ≤ (1 - t / β) • f x + (t / β) •
                (f x + α * ⟪g x, Δ⟫) := by
              gcongr
          _ = f x + α * (t / β) * ⟪g x, Δ⟫ := by
              simp only [smul_eq_mul]
              ring

/-- First-order convexity plus acceptance of the full step forces the
backtracking predicate's selected trial step to equal one. -/
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hfirst : ∀ u v, f u + ⟪g u, v - u⟫ ≤ f v)
    (ht : IsBacktrackingStep f g α β x Δ t)
    (hunit : f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫) :
    t = 1 := by
  exact backtracking_eq_one_of_convexOn_unit_armijo f g α β x Δ t
    (convexOn_univ_of_first_order f g hfirst) hβ0 hβ1 ht hunit
