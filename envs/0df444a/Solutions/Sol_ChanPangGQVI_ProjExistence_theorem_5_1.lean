-- Prove2me | solution 1 for ChanPangGQVI.ProjExistence.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:17:37.589908+00:00
-- url     : https://prove2.me/submissions/bbe9b82e-990d-4188-ac9a-06924263a7bf

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Definitions.Def_ChanPangGQVI_Shared_Projection

open scoped RealInnerProductSpace


namespace ChanPangGQVI.ProjExistence

theorem thm51_core {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (xs ys : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsGQVISolution K f xs ys ↔
      (ChanPangGQVI.Shared.IsProj (K xs) (xs - ys) xs ∧ ys ∈ f xs) := by
  constructor
  · rintro ⟨hx, hy, hvi⟩
    refine ⟨⟨hx, fun q hq => ?_⟩, hy⟩
    have h1 : xs - (xs - ys) = ys := by abel
    have h2 : q - (xs - ys) = (q - xs) + ys := by abel
    rw [h1, h2]
    have hsq : ‖ys‖ ^ 2 ≤ ‖(q - xs) + ys‖ ^ 2 := by
      rw [norm_add_sq_real]
      have := hvi q hq
      nlinarith [sq_nonneg ‖q - xs‖]
    exact le_of_sq_le_sq (by linarith [hsq]) (norm_nonneg _) |> fun h => by
      nlinarith [norm_nonneg ys, norm_nonneg ((q - xs) + ys), sq_nonneg (‖ys‖ - ‖(q - xs) + ys‖)]
  · rintro ⟨⟨hx, hmin⟩, hy⟩
    refine ⟨hx, hy, fun x' hx' => ?_⟩
    by_contra hneg
    push_neg at hneg
    set d := x' - xs
    set c := ⟪d, ys⟫
    set t : ℝ := min 1 (-c / (‖d‖ ^ 2 + 1))
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ -c / (‖d‖ ^ 2 + 1) := min_le_right _ _
    have hmem : xs + t • d ∈ K xs := by
      have := (hK_convex xs).add_smul_sub_mem hx hx' ⟨ht0.le, ht1⟩
      simpa [d] using this
    have hm := hmin _ hmem
    have e1 : xs - (xs - ys) = ys := by abel
    have e2 : xs + t • d - (xs - ys) = t • d + ys := by abel
    rw [e1, e2] at hm
    have hsq : ‖ys‖ ^ 2 ≤ ‖t • d + ys‖ ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hm 2
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
      abs_of_pos ht0] at hsq
    -- t * ‖d‖^2 + 2 c ≥ 0
    have h3 : 0 ≤ t * (t * ‖d‖ ^ 2 + 2 * c) := by nlinarith
    have h4 : 0 ≤ t * ‖d‖ ^ 2 + 2 * c := by
      by_contra h; push_neg at h; nlinarith
    have h5 : t * ‖d‖ ^ 2 ≤ -c := by
      have : t * (‖d‖ ^ 2 + 1) ≤ -c := by
        rw [le_div_iff₀ (by positivity)] at ht2; exact ht2
      nlinarith
    linarith

end ChanPangGQVI.ProjExistence

open ChanPangGQVI.ProjExistence

theorem solution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (xs ys : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsGQVISolution K f xs ys ↔
      (ChanPangGQVI.Shared.IsProj (K xs) (xs - ys) xs ∧ ys ∈ f xs) := by
  exact thm51_core K f hK_closed hK_convex xs ys
