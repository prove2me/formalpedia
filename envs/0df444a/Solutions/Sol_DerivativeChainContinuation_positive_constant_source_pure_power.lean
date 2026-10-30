-- Prove2me | solution 1 for DerivativeChainContinuation.positive_constant_source_pure_power
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:12:29.522992+00:00
-- url     : https://prove2.me/submissions/0fc908a7-2c60-4c51-81d1-b57599dca4a1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp
























end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial







theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring









end DerivativeChainPrivate

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : Q.natDegree=0) (hp : fromRoots a=spokePoly k r Q) :
    fromRoots a=X^(n+1) := by
  have hQC := eq_C_of_natDegree_eq_zero hQdegree
  have hr : r=n+1 := by
    have h := spoke_natDegree k r Q hQ.1 (by omega)
    rw [hQdegree,mul_zero,add_zero,←hp,actual_complex_source_natDegree] at h
    exact h.symm
  have hp' : fromRoots a=X^r*C (Q.coeff 0 : ℂ) := by
    rw [hp,hQC]
    simp only [spokePoly,Polynomial.map_C,Complex.ofRealHom_eq_coe,Polynomial.C_comp,coeff_C_zero]
  have hmonic : (fromRoots a).Monic := Polynomial.monic_prod_X_sub_C a Finset.univ
  have hcoeff : (Q.coeff 0 : ℂ)=1 := by
    have h := congrArg Polynomial.leadingCoeff hp'
    rw [hmonic.leadingCoeff,leadingCoeff_mul,leadingCoeff_X_pow,leadingCoeff_C,one_mul] at h
    exact h.symm
  rw [hp',hcoeff,C_1,mul_one,hr]
