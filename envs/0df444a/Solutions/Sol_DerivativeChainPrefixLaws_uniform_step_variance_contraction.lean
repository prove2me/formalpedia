-- Prove2me | solution 1 for DerivativeChainPrefixLaws.uniform_step_variance_contraction
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:37:51.887924+00:00
-- url     : https://prove2.me/submissions/0bad896c-d39b-4eb1-aa0d-7e3de4a432c4

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_product_nonneg
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem roots_fin_product {n : ℕ} (a : Fin n → ℂ) :
    (∏ i, (X-C (a i))).roots = Finset.univ.val.map a := by
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using
    roots_multiset_prod_X_sub_C (Finset.univ.val.map a)







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem product_rootVariance {n : ℕ} (a : Fin n → ℂ) :
    rootVariance (∏ i, (X-C (a i))) = secondMoment a := by
  simp only [rootVariance, roots_fin_product, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin, Multiset.map_map, secondMoment]
  rfl









end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





theorem complex_root_product_shift (n : ℕ) (a : Fin n → ℂ) (z : ℂ) :
    (∏ i,(X-C (a i-z)))=(∏ i,(X-C (a i))).comp (X+C z) := by
  simp only [Polynomial.prod_comp,sub_comp,X_comp,C_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_sub]
  ring

theorem monicDerivative_translate (p : Polynomial ℂ) (z : ℂ) :
    monicDerivative (p.comp (X+C z))=(monicDerivative p).comp (X+C z) := by
  simp [monicDerivative,Polynomial.natDegree_comp,derivative_comp,Polynomial.mul_comp]
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section





theorem uniform_step_monicDerivative (r : ComplexRootRows) (k : ℕ)
    (hstep : UniformPolynomialStep r k) :
    monicDerivative (complexRowProduct r (k+1))=complexRowProduct r k := by
  have hd : (complexRowProduct r (k+1)).natDegree=k+2 := by simp [complexRowProduct]
  have hn : (k+2:ℂ) ≠ 0 := by exact_mod_cast (show k+2 ≠ 0 by omega)
  rw [monicDerivative,hd,hstep.1]
  push_cast
  rw [← mul_assoc,← C_mul,inv_mul_cancel₀ hn,map_one,one_mul]

theorem uniform_step_shifted_monicDerivative (r : ComplexRootRows) (k : ℕ)
    (hstep : UniformPolynomialStep r k) (u : ℂ) :
    monicDerivative (∏ i : Fin (k+2), (X-C (r (k+1) i-u)))=
      ∏ j : Fin (k+1), (X-C (r k j-u)) := by
  rw [complex_root_product_shift,monicDerivative_translate]
  change (monicDerivative (complexRowProduct r (k+1))).comp (X+C u)=_
  rw [uniform_step_monicDerivative r k hstep]
  exact (complex_root_product_shift (k+1) (r k) u).symm









end
end DerivativeChainPrefixLaws


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
open DerivativeChainPrefixLaws










theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (k : ℕ)
    (hstep : _root_.DerivativeChainContinuation.UniformPolynomialStep r k) (u : ℂ)
    (hc : _root_.DerivativeChainContinuation.complexCentroid (r (k+1))=u) :
    (k+1:ℝ)*_root_.DerivativeChainContinuation.secondMoment (fun j : Fin (k+1) => r k j-u) ≤
      (k:ℝ)*_root_.DerivativeChainContinuation.secondMoment (fun i : Fin (k+2) => r (k+1) i-u) := by
  have hn : (k+2:ℂ) ≠ 0 := by exact_mod_cast (show k+2 ≠ 0 by omega)
  norm_num [_root_.DerivativeChainContinuation.complexCentroid,add_assoc] at hc
  have hmean : (∑ i : Fin (k+2), r (k+1) i)=u*(k+2:ℂ) := by
    exact (div_eq_iff hn).mp hc
  have hzero : (∑ i : Fin (k+2), (r (k+1) i-u))=0 := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,hmean]
    push_cast
    ring
  have hδ := _root_.DerivativeChainContinuation.schoenbergDeficit_product_nonneg (n := k+2) (by omega)
    (fun i : Fin (k+2) => r (k+1) i-u) hzero
  have hd : (∏ i : Fin (k+2), (X-C (r (k+1) i-u))).natDegree=k+2 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      natDegree_finsetProd_X_sub_C_eq_card Finset.univ (fun i : Fin (k+2) => r (k+1) i-u)
  rw [_root_.DerivativeChainContinuation.schoenbergDeficit,hd,_root_.DerivativeChainPrefixLaws.uniform_step_shifted_monicDerivative r k hstep u,
    _root_.DerivativeChainContinuation.product_rootVariance,_root_.DerivativeChainContinuation.product_rootVariance] at hδ
  rw [show k+2-2=k by omega,show k+2-1=k+1 by omega] at hδ
  simpa only [Nat.cast_add,Nat.cast_one] using (sub_nonneg.mp hδ)
