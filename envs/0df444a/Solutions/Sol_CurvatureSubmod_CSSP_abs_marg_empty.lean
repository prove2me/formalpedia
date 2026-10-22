-- Prove2me | solution 1 for CurvatureSubmod.CSSP.abs_marg_empty
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:15:33.81618+00:00
-- url     : https://prove2.me/submissions/90054363-55e1-4e9e-bf86-801d32023ba7

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

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
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

