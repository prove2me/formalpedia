-- Prove2me | solution 1 for CurvatureSubmod.CSSP.fA_monoDec
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:15:18.075208+00:00
-- url     : https://prove2.me/submissions/8a39a095-a4ad-48af-a020-1d1a6cb33323

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

theorem norm_proj_mono {m : ℕ} {K L : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (h : K ≤ L)
    (v : EuclideanSpace ℝ (Fin m)) :
    ‖K.starProjection v‖ ≤ ‖L.starProjection v‖ := by
  have := Submodule.starProjection_comp_starProjection_of_le h
  have h2 : K.starProjection (L.starProjection v) = K.starProjection v := by
    simpa using congrArg (fun T => T v) this
  calc ‖K.starProjection v‖ = ‖K.starProjection (L.starProjection v)‖ := by rw [h2]
    _ ≤ _ := Submodule.norm_starProjection_apply_le _ _

theorem colSpan_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) : colSpan c A ≤ colSpan c B :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem proj_sq_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) (v : EuclideanSpace ℝ (Fin m)) :
    ‖proj c A v‖ ^ 2 ≤ ‖proj c B v‖ ^ 2 := by
  have := norm_proj_mono (colSpan_mono c h) v
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    MonoDec (fA c) := by
  intro A i
  unfold marg
  rw [sol_fA_eq_sum_sub c (insert i A), sol_fA_eq_sum_sub c A, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun j _ => ?_
  have := proj_sq_mono c (Finset.subset_insert i A) (c j)
  linarith

