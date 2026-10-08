-- Prove2me | solution 1 for ConvexOptimization.newton_two_phase_iteration_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T08:38:27.815318+00:00
-- url     : https://prove2.me/submissions/ab9145ef-dd90-471e-8a67-687fff9ac42f

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Definitions.Def_ConvexOptimization_IsDampedNewtonSequence
import Theorems.Thm_ConvexOptimization_hessian_lower_bound_implies_strong_convexity
import Theorems.Thm_ConvexOptimization_strong_convexity_quadratic_lower_bound
import Theorems.Thm_ConvexOptimization_newton_damped_phase_decrease
import Theorems.Thm_ConvexOptimization_newton_quadratic_phase_contraction
import Theorems.Thm_ConvexOptimization_backtracking_selects_unit_of_armijo
import Theorems.Thm_ConvexOptimization_two_phase_iteration_count_of_suboptimality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ} (m M L α β ε : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hL : 0 < L)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε0 : 0 < ε) (hεsmall : ε ≤ m ^ 3 / (2 * L ^ 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hnewton : ConvexOptimization.IsDampedNewtonSequence f g H α β x)
    (K : ℕ)
    (hK : (f (x 0) - f xstar) /
        (α * β * (min 1 (3 * (1 - 2 * α)) * m ^ 2 / L) ^ 2 * m / M ^ 2) +
        Real.logb 2 (Real.logb 2 (2 * m ^ 3 / L ^ 2 / ε)) ≤ (K : ℝ)) :
    f (x K) - f xstar ≤ ε := by
  let η : ℝ := min 1 (3 * (1 - 2 * α)) * m ^ 2 / L
  let decrease : ℝ := α * β * η ^ 2 * m / M ^ 2
  let scale : ℝ := L / (2 * m ^ 2)
  let ε₀ : ℝ := 2 * m ^ 3 / L ^ 2
  have hηdef : η = min 1 (3 * (1 - 2 * α)) * m ^ 2 / L := rfl
  have hc0 : 0 < min 1 (3 * (1 - 2 * α)) := by
    rw [lt_min_iff]
    constructor <;> nlinarith
  have hη0 : 0 < η := by
    rw [hηdef]
    exact div_pos (mul_pos hc0 (sq_pos_of_pos hm)) hL
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hdecrease0 : 0 < decrease := by
    dsimp [decrease]
    positivity
  have hscale0 : 0 < scale := by
    dsimp [scale]
    positivity
  have hε₀0 : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hεsmall' : ε ≤ ε₀ / 4 := by
    calc
      ε ≤ m ^ 3 / (2 * L ^ 2) := hεsmall
      _ = ε₀ / 4 := by dsimp [ε₀]; ring
  have hnormalization : ε₀ * scale ^ 2 = 1 / (2 * m) := by
    dsimp [ε₀, scale]
    field_simp [ne_of_gt hm, ne_of_gt hL]
  have hscaledThreshold : scale * η ≤ 1 / 2 := by
    have heq : scale * η = min 1 (3 * (1 - 2 * α)) / 2 := by
      dsimp [scale, η]
      field_simp [ne_of_gt hm, ne_of_gt hL]
    rw [heq]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hsc : ∀ u v : EuclideanSpace ℝ (Fin n),
      f u + ⟪g u, v - u⟫ + m / 2 * ‖v - u‖ ^ 2 ≤ f v := by
    intro u v
    exact ConvexOptimization.hessian_lower_bound_implies_strong_convexity
      m f g hg H hH hHm u v
  have hfirst : ∀ u v : EuclideanSpace ℝ (Fin n),
      f u + ⟪g u, v - u⟫ ≤ f v := by
    intro u v
    have h := hsc u v
    have hnonneg : 0 ≤ m / 2 * ‖v - u‖ ^ 2 := by positivity
    linarith
  refine ConvexOptimization.two_phase_iteration_count_of_suboptimality
    (fun k => f (x k) - f xstar) (fun k => ‖g (x k)‖)
    m decrease scale η ε₀ ε hm hdecrease0 hscale0 hη0 hε₀0 hε0
    hεsmall' hnormalization hscaledThreshold ?_ ?_ ?_ ?_ ?_ K ?_
  · intro k
    exact sub_nonneg.mpr (hstar (Set.mem_univ (x k)))
  · intro k
    exact norm_nonneg _
  · intro k hk
    rcases hnewton k with ⟨Δ, t, hΔ, ht, hstep⟩
    have hd := ConvexOptimization.newton_damped_phase_decrease
      m M L α β η hm hmM hL hα0 hα hβ0 hβ1 hηdef
      f g hg H hH hHm hHM hHL (x k) Δ t hΔ hk ht
    rw [hstep]
    dsimp [decrease]
    linarith
  · intro k hk
    rcases hnewton k with ⟨Δ, t, hΔ, ht, hstep⟩
    rcases ConvexOptimization.newton_quadratic_phase_contraction
        m M L α β η hm hmM hL hα0 hα hβ0 hβ1 hηdef
        f g hg H hH hHm hHM hHL (x k) Δ hΔ hk with ⟨hunit, hquad⟩
    have ht1 : t = 1 :=
      ConvexOptimization.backtracking_selects_unit_of_armijo
        f g α β (x k) Δ t hβ0 hβ1 hfirst ht hunit
    have hstep' : x (k + 1) = x k + Δ := by
      simpa [ht1] using hstep
    rw [hstep']
    simpa [scale] using hquad
  · intro k
    exact ConvexOptimization.strong_convexity_quadratic_lower_bound
      m hm f g hg hsc xstar hstar (x k)
  · simpa [decrease, η, ε₀] using hK
