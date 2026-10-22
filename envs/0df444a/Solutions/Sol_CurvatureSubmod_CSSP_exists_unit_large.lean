-- Prove2me | solution 1 for CurvatureSubmod.CSSP.exists_unit_large
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:19.770563+00:00
-- url     : https://prove2.me/submissions/214391e4-d7ca-439c-89d2-a68bb62b07ad

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting
set_option autoImplicit false
open CurvatureSubmod.CSSP

theorem pyth {m : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (v : EuclideanSpace ℝ (Fin m)) :
    ‖v - K.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - ‖K.starProjection v‖ ^ 2 := by
  have h1 : K.starProjection v ∈ K := Submodule.starProjection_apply_mem K v
  have h2 : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : inner ℝ (K.starProjection v) (v - K.starProjection v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal h1 h2
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (K.starProjection v)
    (v - K.starProjection v) h3
  rw [add_sub_cancel] at this
  rw [sq, sq, sq]
  linarith

theorem sol_fA_eq_sum_sub {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    fA c S = ∑ i, (‖c i‖ ^ 2 - ‖proj c S (c i)‖ ^ 2) := by
  unfold fA
  exact Finset.sum_congr rfl fun i _ => pyth (colSpan c S) (c i)

theorem proj_empty {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    proj c ∅ x = 0 := by
  unfold proj colSpan
  simp

theorem sol_abs_marg_empty {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) ∅ i| = ∑ j, ‖proj c {i} (c j)‖ ^ 2 := by
  unfold marg
  rw [Finset.insert_empty, sol_fA_eq_sum_sub c {i}, sol_fA_eq_sum_sub c ∅, ← Finset.sum_sub_distrib]
  have : ∀ j, ‖c j‖ ^ 2 - ‖proj c {i} (c j)‖ ^ 2 - (‖c j‖ ^ 2 - ‖proj c ∅ (c j)‖ ^ 2) =
      -‖proj c {i} (c j)‖ ^ 2 := by
    intro j
    rw [proj_empty]
    simp
  simp_rw [this]
  rw [Finset.sum_neg_distrib, abs_neg]
  exact abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem applyA_smul {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : applyA c (r • x) = r • applyA c x := by
  simp [applyA, Finset.smul_sum, smul_smul]

theorem norm_proj_single_sq {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i j : Fin n) :
    ‖proj c {i} (c j)‖ ^ 2 = (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 := by
  have : proj c {i} (c j) = (inner ℝ (c i) (c j) / ((‖c i‖ ^ 2 : ℝ) : ℝ)) • c i := by
    unfold proj colSpan
    simp only [Finset.coe_singleton, Set.image_singleton]
    exact Submodule.starProjection_singleton ℝ (c j)
  rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow]
  by_cases h0 : c i = 0
  · simp [h0]
  · have : ‖c i‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    field_simp

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      Real.sqrt |marg (fA c) ∅ i| ≤ ‖applyA c x‖ := by
  rw [sol_abs_marg_empty]
  simp_rw [norm_proj_single_sq]
  set w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => inner ℝ (c i) (c j)) with hw
  have hw2 : ‖w‖ ^ 2 = ∑ j, (inner ℝ (c i) (c j)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hw]
  have hsingle : ‖(EuclideanSpace.single i (1:ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
  by_cases hw0 : ‖w‖ = 0
  · refine ⟨EuclideanSpace.single i 1, hsingle, ?_⟩
    have : ∑ j, (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 = 0 := by
      rw [← Finset.sum_div, ← hw2, hw0]; simp
    rw [this]; simp
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
    have hc0 : c i ≠ 0 := by
      intro h
      apply hw0
      have : ∑ j, (inner ℝ (c i) (c j)) ^ 2 = 0 := by simp [h]
      rw [← hw2] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hcpos : 0 < ‖c i‖ := norm_pos_iff.mpr hc0
    refine ⟨(‖w‖⁻¹) • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hw0
    · rw [applyA_smul, norm_smul, norm_inv, norm_norm]
      have hinner : inner ℝ (c i) (applyA c w) = ‖w‖ ^ 2 := by
        rw [hw2]
        simp [applyA, inner_sum, inner_smul_right, hw, sq]
      have hcs : ‖w‖ ^ 2 ≤ ‖c i‖ * ‖applyA c w‖ := by
        rw [← hinner]
        exact real_inner_le_norm _ _
      have hs : ∑ j, (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 = (‖w‖ / ‖c i‖) ^ 2 := by
        rw [← Finset.sum_div, ← hw2, div_pow]
      rw [hs, Real.sqrt_sq (by positivity)]
      rw [div_le_iff₀ hcpos, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hwpos]
      nlinarith

