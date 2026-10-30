-- Prove2me | solution 1 for DerivativeChainContinuation.uniform_polynomial_tower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:54:36.026636+00:00
-- url     : https://prove2.me/submissions/1bb00654-70cf-4b94-bf6f-b6957d80f046

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_constant_unitary_tail_marginal
import Theorems.Thm_DerivativeChainContinuation_exists_constant_first_schur
import Theorems.Thm_DerivativeChainContinuation_pinned_schur_derivative_factorization
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


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


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem uniform_root_transport (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ) :
    ∃ (b : Fin n → ℂ) (K : Fin n → Fin (n+1) → ℝ),
      monicDerivative (∏ i, (X-C (a i))) = ∏ j, (X-C (b j)) ∧
      (∀ j i, 0 ≤ K j i) ∧ (∀ j, ∑ i, K j i=1) ∧
      (∀ j, ∑ i, (K j i:ℂ)*a i=b j) ∧
      (∀ i, (∑ j, (n:ℝ)⁻¹*K j i)=(n+1:ℝ)⁻¹) := by
  obtain ⟨Q,hQ,hfirst,ht⟩ := exists_constant_first_schur n a
  refine ⟨(fun j => (Q.conjTranspose*diagonal a*Q) j.succ j.succ),
    (fun j i => Complex.normSq (Q i j.succ)),
    pinned_schur_derivative_factorization n a Q hQ hfirst ht,?_,?_,?_,?_⟩
  · intro j i; exact Complex.normSq_nonneg _
  · intro j; exact unitary_column_normSq_sum Q hQ j.succ
  · intro j; exact unitary_diagonal_mean a Q j.succ
  · intro i; exact constant_unitary_tail_marginal n hn Q hQ hfirst i
end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ r : ComplexRootRows, r n=a ∧ ∀ k<n, UniformPolynomialStep r k := by
  classical
  induction n with
  | zero =>
    refine ⟨(fun _ _ => a 0),?_,?_⟩
    · funext i
      rw [show i=0 from Fin.eq_zero i]
    · intro k hk; omega
  | succ n ih =>
    obtain ⟨b,K,hpoly,hK,hKs,hKm,hKcol⟩ := uniform_root_transport (n+1) (by omega) a
    have hd : (∏ i, (X-C (a i))).natDegree=n+2 := by simp
    have hnC : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
    have hder : derivative (∏ i, (X-C (a i)))=C (n+2:ℂ)*(∏ j, (X-C (b j))) := by
      rw [← hpoly,monicDerivative,hd]
      push_cast
      rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hnC,map_one,one_mul]
    obtain ⟨r,htop,hstep⟩ := ih b
    let rr : ComplexRootRows := Function.update r (n+1) a
    have hrr (k : ℕ) (hk : k ≤ n) : rr k=r k := by
      simp [rr,Function.update_of_ne (show k ≠ n+1 by omega)]
    have hnew : rr (n+1)=a := by simp [rr]
    refine ⟨rr,hnew,?_⟩
    intro k hk
    by_cases he : k=n
    · subst k
      simp only [UniformPolynomialStep,complexRowProduct,hnew,hrr n le_rfl,htop]
      refine ⟨hder,K,hK,hKs,hKm,?_⟩
      convert hKcol using 1 <;> norm_num [Nat.cast_add,Nat.cast_one,add_assoc]
    · simpa only [UniformPolynomialStep,complexRowProduct,hrr k (by omega),hrr (k+1) (by omega)]
        using hstep k (by omega)
