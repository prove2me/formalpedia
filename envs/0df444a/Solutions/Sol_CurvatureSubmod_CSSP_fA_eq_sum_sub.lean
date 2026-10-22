-- Prove2me | solution 1 for CurvatureSubmod.CSSP.fA_eq_sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:54.402082+00:00
-- url     : https://prove2.me/submissions/bc562de8-a118-4e02-bfc6-d4618d08f807

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

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    fA c S = ∑ i, (‖c i‖ ^ 2 - ‖proj c S (c i)‖ ^ 2) := by
  unfold fA
  exact Finset.sum_congr rfl fun i _ => pyth (colSpan c S) (c i)

