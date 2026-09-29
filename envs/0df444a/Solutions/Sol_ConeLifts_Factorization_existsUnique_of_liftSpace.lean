-- Prove2me | solution 1 for ConeLifts.Factorization.existsUnique_of_liftSpace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:37:45.537985+00:00
-- url     : https://prove2.me/submissions/a2d17800-954e-4ccf-99f5-b77a269fa7bd

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

lemma aux_eul_polar_convex {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConeLifts.Shared.polar C) := by
  intro y1 hy1 y2 hy2 a b ha hb hab x hx
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := hy1 x hx
  have h2 := hy2 x hx
  nlinarith

lemma aux_eul_polar_closed {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConeLifts.Shared.polar C) := by
  have : ConeLifts.Shared.polar C = ⋂ x ∈ C, {y | ⟪x, y⟫_ℝ ≤ 1} := by
    ext y; simp [ConeLifts.Shared.polar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma aux_eul_polar_bounded {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    Bornology.IsBounded (ConeLifts.Shared.polar C) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hC)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 / δ, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hy0 : y = 0
  · simp [hy0]; positivity
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hx : (δ / 2 / ‖y‖) • y ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hyn.ne']
    linarith
  have := hy _ hx
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at this
  have h2 : δ / 2 / ‖y‖ * ‖y‖ ^ 2 = δ / 2 * ‖y‖ := by
    field_simp
  rw [h2] at this
  rw [le_div_iff₀ hδ]
  nlinarith

theorem aux_eul_main {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (w : EuclideanSpace ℝ (Fin n))
    (hw : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ⟪w, y⟫_ℝ = 0) :
    w = 0 := by
  set P := ConeLifts.Shared.polar C
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded
    (aux_eul_polar_closed C) (aux_eul_polar_bounded C hC.2.2)
  have hPconv : Convex ℝ P := aux_eul_polar_convex C
  let H : Set (EuclideanSpace ℝ (Fin n)) := {y | ⟪w, y⟫_ℝ = 0}
  have hHc : IsClosed H := isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hHconv : Convex ℝ H := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [H, Set.mem_setOf_eq] at hy1 hy2 ⊢
    rw [inner_add_right, inner_smul_right, inner_smul_right, hy1, hy2]
    ring
  have hPH : P ⊆ H := by
    rw [← closure_convexHull_extremePoints hPc hPconv]
    exact closure_minimal (convexHull_min (fun y hy => hw y hy) hHconv) hHc
  obtain ⟨R, hR⟩ := hC.1.isBounded.exists_norm_le
  set R' := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  set ε := 1 / (R' * (‖w‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεw : ε • w ∈ P := by
    intro x hx
    rw [real_inner_smul_right]
    have h1 : ⟪x, w⟫_ℝ ≤ ‖x‖ * ‖w‖ := real_inner_le_norm x w
    have h2 : ‖x‖ ≤ R' := by
      have := hR x hx
      have := le_max_left R 0
      linarith
    have h3 : ⟪x, w⟫_ℝ ≤ R' * (‖w‖ + 1) := by
      calc ⟪x, w⟫_ℝ ≤ ‖x‖ * ‖w‖ := h1
        _ ≤ R' * ‖w‖ := by gcongr
        _ ≤ R' * (‖w‖ + 1) := by nlinarith
    have h4 : ε * (R' * (‖w‖ + 1)) = 1 := by
      rw [hε]; field_simp
    nlinarith
  have := hPH hεw
  simp only [H, Set.mem_setOf_eq, real_inner_smul_right] at this
  have h5 : ⟪w, w⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hεpos.ne'
    · exact h
  exact inner_self_eq_zero.mp h5

end ConeLifts.Factorization

open ConeLifts.Factorization

theorem solution {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (hzL : ∃ x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) :
    ∃! x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ := by
  obtain ⟨x0, hx0⟩ := hzL
  refine ⟨x0, hx0, fun x1 hx1 => ?_⟩
  have hw : x1 - x0 = 0 := by
    apply aux_eul_main C hC
    intro y hy
    rw [inner_sub_left]
    have h0 := hx0 y hy
    have h1 := hx1 y hy
    linarith
  exact sub_eq_zero.mp hw
