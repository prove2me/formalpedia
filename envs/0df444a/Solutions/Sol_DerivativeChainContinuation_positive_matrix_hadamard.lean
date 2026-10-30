-- Prove2me | solution 1 for DerivativeChainContinuation.positive_matrix_hadamard
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:02:13.712504+00:00
-- url     : https://prove2.me/submissions/a0ca4067-c0fc-49f9-b4ce-be7529cf8e35

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_doubly_stochastic_product_bound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem unitary_column_normSq_sum {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq (Q i j)=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j j)
    (mem_unitaryGroup_iff'.mp hQ)
  simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one,
    Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
    Matrix.one_apply,if_pos rfl,ite_true] using h

theorem unitary_row_normSq_sum {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq (Q i j)=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i)
    (mem_unitaryGroup_iff.mp hQ)
  simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one,
    Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
    Matrix.one_apply,if_pos rfl,ite_true,mul_comm] using h

theorem unitary_diagonal_mean {n : ℕ} (a : Fin n → ℂ)
    (Q : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (∑ i, (Complex.normSq (Q i j):ℂ)*a i)=(Q.conjTranspose*diagonal a*Q) j j := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply,Matrix.conjTranspose_apply,
    Complex.star_def,Complex.normSq_eq_conj_mul_self,ite_mul,mul_ite,zero_mul,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) : ‖A.det‖ ≤ ∏ i, (A i i).re := by
  let U : Matrix (Fin n) (Fin n) ℂ := hA.isHermitian.eigenvectorUnitary
  let v : Fin n → ℝ := hA.isHermitian.eigenvalues
  have hv (j : Fin n) : 0 < v j := hA.eigenvalues_pos j
  have hU : U ∈ unitaryGroup (Fin n) ℂ := hA.isHermitian.eigenvectorUnitary.property
  have hUs : U.conjTranspose ∈ unitaryGroup (Fin n) ℂ := by
    apply mem_unitaryGroup_iff.mpr
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  have hs : A=U*diagonal (fun j => (v j:ℂ))*U.conjTranspose := by
    simpa [U,v,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_def] using
      hA.isHermitian.spectral_theorem
  have hm (i : Fin n) : (∑ j, Complex.normSq (U.conjTranspose j i)*v j)=(A i i).re := by
    have hh := unitary_diagonal_mean (fun j => (v j:ℂ)) U.conjTranspose i
    simp only [Matrix.conjTranspose_conjTranspose,← hs] at hh
    simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero] using congrArg Complex.re hh
  have hd : ‖A.det‖=∏ j, v j := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues,norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    simpa [v,RCLike.norm_ofReal] using abs_of_pos (hv j)
  rw [hd]
  have hh := doubly_stochastic_product_bound
    (fun i j => Complex.normSq (U.conjTranspose j i)) v
    (fun _ _ => Complex.normSq_nonneg _)
    (fun i => unitary_column_normSq_sum _ hUs i)
    (fun j => unitary_row_normSq_sum _ hUs j) hv
  simpa only [hm] using hh
