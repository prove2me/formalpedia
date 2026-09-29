-- Prove2me | solution 1 for ConeLifts.Factorization.mem_of_liftSpace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:38:15.1313+00:00
-- url     : https://prove2.me/submissions/4587b73a-48c4-42c9-ac88-98280504e8d4

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

lemma aux_mol_polar_convex {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConeLifts.Shared.polar S) := by
  intro y hy y' hy' a b ha hb hab x hx
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := hy x hx
  have h2 := hy' x hx
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma aux_mol_polar_closed {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConeLifts.Shared.polar S) := by
  have : ConeLifts.Shared.polar S = ⋂ x ∈ S, {y | ⟪x, y⟫_ℝ ≤ 1} := by
    ext y; simp [ConeLifts.Shared.polar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma aux_mol_polar_compact {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    IsCompact (ConeLifts.Shared.polar C) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply Metric.isCompact_of_isClosed_isBounded (aux_mol_polar_closed C)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 / r, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hy0 : y = 0
  · simp [hy0]; positivity
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have ha : (r / 2 / ‖y‖) • y ∈ C := hball (by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
    linarith)
  have := hy _ ha
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at this
  have h3 : r / 2 / ‖y‖ * ‖y‖ ^ 2 = r / 2 * ‖y‖ := by field_simp
  rw [h3] at this
  rw [le_div_iff₀ hr]
  linarith

end ConeLifts.Factorization

open ConeLifts.Factorization
open scoped InnerProductSpace

theorem solution {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K)
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (hxz : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) :
    x ∈ C := by
  obtain ⟨hCc, hCconv, h0⟩ := hC
  have hH : ∀ y ∈ ConeLifts.Shared.polar C, ⟪x, y⟫_ℝ ≤ 1 := by
    have hsub : Set.extremePoints ℝ (ConeLifts.Shared.polar C) ⊆ ConeLifts.Shared.polar {x} := by
      intro y hy w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h1 := hxz y hy
      have h2 := hB y hy z hz
      linarith
    have hsub2 : ConeLifts.Shared.polar C ⊆ ConeLifts.Shared.polar {x} := by
      rw [← closure_convexHull_extremePoints (aux_mol_polar_compact C h0)
        (aux_mol_polar_convex C)]
      exact closure_minimal (convexHull_min hsub (aux_mol_polar_convex {x}))
        (aux_mol_polar_closed {x})
    intro y hy
    exact hsub2 hy x rfl
  by_contra hx
  obtain ⟨f, u, hfa, hfx⟩ := geometric_hahn_banach_closed_point hCconv hCc.isClosed hx
  have hu : 0 < u := by simpa using hfa 0 (interior_subset h0)
  set y : EuclideanSpace ℝ (Fin n) :=
    (1 / u) • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f with hydef
  have key : ∀ a, ⟪a, y⟫_ℝ = f a / u := by
    intro a
    rw [hydef, real_inner_smul_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    ring
  have hy : y ∈ ConeLifts.Shared.polar C := fun a ha => by
    rw [key, div_le_one hu]; exact (hfa a ha).le
  have := hH y hy
  rw [key, div_le_one hu] at this
  linarith
