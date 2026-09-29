-- Prove2me | solution 1 for ConeLifts.Factorization.extremePoint_polar_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:50:22.771858+00:00
-- url     : https://prove2.me/submissions/6c3a04ac-93bd-4081-8291-79c0411db6a1

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- The origin is never an extreme point of the polar of a bounded set in `ℝⁿ`, `n ≥ 1`. -/
theorem aux_epig_zero_not_extreme {n : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hb : Bornology.IsBounded C)
    (hext : ∀ x₁ ∈ ConeLifts.Shared.polar C, ∀ x₂ ∈ ConeLifts.Shared.polar C,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ openSegment ℝ x₁ x₂ → x₁ = 0 ∧ x₂ = 0) : False := by
  obtain ⟨R, hR0, hR⟩ := hb.subset_closedBall_lt 0 0
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by rw [he, PiLp.norm_single]; simp
  set y : EuclideanSpace ℝ (Fin n) := (1 / R) • e with hy
  have hyn : ‖y‖ = 1 / R := by
    rw [hy, norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have habs : ∀ x ∈ C, |⟪x, y⟫_ℝ| ≤ 1 := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa using hR hx
    calc |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
      _ ≤ R * (1 / R) := by
          rw [hyn]; exact mul_le_mul_of_nonneg_right hxR (by positivity)
      _ = 1 := by field_simp
  have hyP : y ∈ ConeLifts.Shared.polar C := fun x hx => (le_abs_self _).trans (habs x hx)
  have hnyP : -y ∈ ConeLifts.Shared.polar C := by
    intro x hx
    rw [inner_neg_right]
    exact (neg_le_abs _).trans (habs x hx)
  have hseg : (0 : EuclideanSpace ℝ (Fin n)) ∈ openSegment ℝ y (-y) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [smul_neg]; exact add_neg_cancel _⟩
  have hy0 : y = 0 := (hext y hyP (-y) hnyP hseg).1
  have : ‖y‖ = 0 := by rw [hy0, norm_zero]
  rw [hyn] at this
  have : (0 : ℝ) < 1 / R := by positivity
  linarith

end ConeLifts.Factorization

open ConeLifts.Factorization

theorem solution {n : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    IsGreatest ((fun x => ⟪c, x⟫_ℝ) '' C) 1 := by
  obtain ⟨hcomp, _hconv, h0⟩ := hC
  have h0C : (0 : EuclideanSpace ℝ (Fin n)) ∈ C := interior_subset h0
  rw [mem_extremePoints] at hc
  obtain ⟨hcP, hext⟩ := hc
  have hub : ∀ x ∈ C, ⟪c, x⟫_ℝ ≤ 1 := fun x hx => by rw [real_inner_comm]; exact hcP x hx
  obtain ⟨x0, hx0C, hx0max⟩ := hcomp.exists_isMaxOn ⟨0, h0C⟩
    ((continuous_const.inner continuous_id).continuousOn :
      ContinuousOn (fun x => ⟪c, x⟫_ℝ) C)
  refine ⟨⟨x0, hx0C, ?_⟩, ?_⟩
  swap
  · rintro _ ⟨x, hx, rfl⟩
    exact hub x hx
  have hmax : ∀ x ∈ C, ⟪c, x⟫_ℝ ≤ ⟪c, x0⟫_ℝ := fun x hx => hx0max hx
  have hs1 : ⟪c, x0⟫_ℝ ≤ 1 := hub x0 hx0C
  have hs0 : 0 ≤ ⟪c, x0⟫_ℝ := by
    have := hmax 0 h0C
    simpa using this
  by_contra hne
  have hlt : ⟪c, x0⟫_ℝ < 1 := lt_of_le_of_ne hs1 hne
  set s := ⟪c, x0⟫_ℝ with hs
  have h0P : (0 : EuclideanSpace ℝ (Fin n)) ∈ ConeLifts.Shared.polar C := by
    intro x _
    simp
  have hc0 : c = 0 := by
    set l : ℝ := 2 / (1 + s) with hl
    have hl1 : 1 < l := by
      rw [hl, lt_div_iff₀ (by linarith)]
      linarith
    have hlc : l • c ∈ ConeLifts.Shared.polar C := by
      intro x hx
      rw [inner_smul_right]
      have hxs : ⟪x, c⟫_ℝ ≤ s := by rw [real_inner_comm]; exact hmax x hx
      calc l * ⟪x, c⟫_ℝ ≤ l * s := mul_le_mul_of_nonneg_left hxs (by linarith)
        _ ≤ 1 := by
            rw [hl, div_mul_eq_mul_div, div_le_one (by linarith)]
            linarith
    have hl0 : l ≠ 0 := by linarith
    have hseg : c ∈ openSegment ℝ 0 (l • c) := by
      refine ⟨1 - 1 / l, 1 / l, ?_, ?_, ?_, ?_⟩
      · have : 1 / l < 1 := by rw [div_lt_one (by linarith)]; exact hl1
        linarith
      · have : 0 < l := by linarith
        positivity
      · ring
      · rw [smul_zero, zero_add, smul_smul, one_div_mul_cancel hl0, one_smul]
    exact (hext 0 h0P (l • c) hlc hseg).1.symm
  subst hc0
  exact aux_epig_zero_not_extreme hn C hcomp.isBounded hext
