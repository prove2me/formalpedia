-- Prove2me | solution 1 for DirectFidelity.RandomState.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:43:44.134886+00:00
-- url     : https://prove2.me/submissions/e7e315d9-90a2-4376-8181-7cf95080ec01

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace BigOperators
open DirectFidelity.State DirectFidelity.RandomState

namespace FidelityResearch

theorem pauli1_unitary (k : Fin 4) : (pauli1 k).conjTranspose * pauli1 k = 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.one_apply, Complex.I_mul_I]

theorem W_unitary {n : ℕ} (k : P n) : (W k).conjTranspose * W k = 1 := by
  classical
  ext x z
  have hlocal (i : Fin n) :
      (∑ a : Fin 2, star (pauli1 (k i) a (x i)) * pauli1 (k i) a (z i)) =
        if x i = z i then 1 else 0 := by
    have hh := congrFun (congrFun (pauli1_unitary (k i)) (x i)) (z i)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hh
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : Fin 2) =>
    star (pauli1 (k i) a (x i)) * pauli1 (k i) a (z i))]
  simp_rw [hlocal]
  change (∏ i, if x i = z i then (1 : ℂ) else 0) = if x = z then 1 else 0
  by_cases h : x = z
  · subst z
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem W_inner {n : ℕ} (k : P n) (x y : E n) :
    inner ℂ (Matrix.toEuclideanLin (W k) x) (Matrix.toEuclideanLin (W k) y) = inner ℂ x y := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec, W_unitary, Matrix.one_mulVec, WithLp.toLp_ofLp]

theorem W_norm {n : ℕ} (k : P n) (x : E n) :
    ‖Matrix.toEuclideanLin (W k) x‖ = ‖x‖ := by
  simp only [@norm_eq_sqrt_re_inner ℂ, W_inner]

end FidelityResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Flammia and Liu, arXiv:1104.4695v3, equation (36).
theorem solution {n : ℕ} (k : DirectFidelity.State.P n) (ψ ψ' : DirectFidelity.RandomState.E n)
    (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) :
    ‖pauliExp k ψ - pauliExp k ψ'‖ ≤
        ‖inner ℂ ψ (Matrix.toEuclideanLin (W k) (ψ - ψ'))‖ +
          ‖inner ℂ (ψ - ψ') (Matrix.toEuclideanLin (W k) ψ')‖ ∧
      ‖inner ℂ ψ (Matrix.toEuclideanLin (W k) (ψ - ψ'))‖ +
          ‖inner ℂ (ψ - ψ') (Matrix.toEuclideanLin (W k) ψ')‖ ≤ 2 * ‖ψ - ψ'‖ := by
  constructor
  · have hid : pauliExp k ψ - pauliExp k ψ' =
        inner ℂ ψ (Matrix.toEuclideanLin (W k) (ψ - ψ')) +
          inner ℂ (ψ - ψ') (Matrix.toEuclideanLin (W k) ψ') := by
      simp only [pauliExp, map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [hid]
    exact norm_add_le _ _
  · have h1 := norm_inner_le_norm (𝕜 := ℂ) ψ (Matrix.toEuclideanLin (W k) (ψ - ψ'))
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (ψ - ψ') (Matrix.toEuclideanLin (W k) ψ')
    rw [FidelityResearch.W_norm, hψ] at h1
    rw [FidelityResearch.W_norm, hψ'] at h2
    linarith
