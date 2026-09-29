-- Prove2me | solution 1 for ConeLifts.Factorization.zero_not_mem_liftSpace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:58:06.76198+00:00
-- url     : https://prove2.me/submissions/f227a768-ef65-4ba0-a662-273dd26c658f

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

theorem aux_znml_polar_isClosed {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConeLifts.Shared.polar C) := by
  have : ConeLifts.Shared.polar C = ⋂ x ∈ C, {y : EuclideanSpace ℝ (Fin n) | ⟪x, y⟫_ℝ ≤ 1} := by
    ext y; simp [ConeLifts.Shared.polar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem aux_znml_polar_convex {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConeLifts.Shared.polar C) := by
  intro y1 hy1 y2 hy2 a b ha hb hab x hx
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := hy1 x hx
  have h2 := hy2 x hx
  nlinarith

theorem aux_znml_polar_bounded {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    Bornology.IsBounded (ConeLifts.Shared.polar C) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0
  obtain ⟨r, hr, hball⟩ := h0
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 / r, fun y hy => ?_⟩
  by_cases hy0 : y = 0
  · subst hy0; simp; positivity
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set x : EuclideanSpace ℝ (Fin n) := (r / 2 / ‖y‖) • y with hxdef
  have hxmem : x ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, hxdef, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [div_mul_cancel₀ _ hyn.ne']
    linarith
  have hle := hy x hxmem
  rw [hxdef, real_inner_smul_left, real_inner_self_eq_norm_sq] at hle
  have : r / 2 / ‖y‖ * ‖y‖ ^ 2 = r / 2 * ‖y‖ := by
    field_simp
  rw [this] at hle
  rw [le_div_iff₀ hr]
  nlinarith

end ConeLifts.Factorization

open ConeLifts.Factorization

open scoped InnerProductSpace

theorem solution {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (0 : EuclideanSpace ℝ (Fin m)) ∉
      {z : EuclideanSpace ℝ (Fin m) | ∃ x : EuclideanSpace ℝ (Fin n),
        ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ} := by
  rintro ⟨x, hx⟩
  obtain ⟨_, _, h0⟩ := hC
  have hcomp : IsCompact (ConeLifts.Shared.polar C) :=
    Metric.isCompact_of_isClosed_isBounded (aux_znml_polar_isClosed C)
      (aux_znml_polar_bounded C h0)
  have hconv := aux_znml_polar_convex C
  set H : Set (EuclideanSpace ℝ (Fin n)) := {y | ⟪x, y⟫_ℝ = 1} with hH
  have hHclosed : IsClosed H :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hHconv : Convex ℝ H := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [hH, Set.mem_ofPred_eq] at hy1 hy2 ⊢
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hy1, hy2]
    linarith
  have hext : Set.extremePoints ℝ (ConeLifts.Shared.polar C) ⊆ H := by
    intro y hy
    have := hx y hy
    simp only [inner_zero_left] at this
    simp only [hH, Set.mem_ofPred_eq]
    linarith
  have hsub : ConeLifts.Shared.polar C ⊆ H := by
    rw [← closure_convexHull_extremePoints hcomp hconv]
    exact closure_minimal (convexHull_min hext hHconv) hHclosed
  have h0p : (0 : EuclideanSpace ℝ (Fin n)) ∈ ConeLifts.Shared.polar C := by
    intro x' _; simp
  have := hsub h0p
  simp [hH] at this
