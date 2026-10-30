-- Prove2me | solution 1 for DerivativeChainContinuation.coefficient_gap_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:09:07.00309+00:00
-- url     : https://prove2.me/submissions/010a17f6-ac32-4cb0-9948-692bab9e57e8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_sparse_appell_chain_bound
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial







theorem centeredSource_natDegree (p : Polynomial ℂ) :
    (centeredSource p).natDegree = p.natDegree := by
  rw [centeredSource, natDegree_comp, natDegree_X_add_C, mul_one]

theorem centeredSource_monic (p : Polynomial ℂ) (hp : p.Monic) :
    (centeredSource p).Monic := hp.comp_X_add_C _






end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem appellRow_coeff (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = if k ≤ m then (m.choose k:ℂ)*c (m-k) else 0 := by
  classical
  simp only [appellRow,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq',Nat.lt_succ_iff]

theorem appellRow_coeff_eq (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = (m.choose k:ℂ)*c (m-k) := by
  rw [appellRow_coeff]
  split_ifs with hk
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]











end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators











theorem chainCost_cast_index {n m : ℕ} (h : n=m) (z : Fin m → ℂ) :
    chainCost (fun i : Fin n => z (Fin.cast h i))=chainCost z := by
  subst m
  rfl

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem appellCoefficients_zero (p : Polynomial ℂ) (hp : p.Monic) :
    appellCoefficients p 0=1 := by
  simpa [appellCoefficients] using hp.leadingCoeff

theorem appellRow_coefficients (p : Polynomial ℂ) :
    appellRow p.natDegree (appellCoefficients p)=p := by
  ext k
  rw [appellRow_coeff_eq]
  by_cases hk : k ≤ p.natDegree
  · have hn : (p.natDegree.choose k:ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
    unfold appellCoefficients
    rw [Nat.sub_sub_self hk,Nat.choose_symm hk]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem translatedAppell_centeredSource (p : Polynomial ℂ) :
    (appellRow p.natDegree (appellCoefficients (centeredSource p))).comp (X-C (rootCentroid p))=p := by
  rw [← centeredSource_natDegree p,appellRow_coefficients,centeredSource,comp_assoc]
  have he : (X+C (rootCentroid p)).comp (X-C (rootCentroid p)) = (X:Polynomial ℂ) := by simp
  rw [he,comp_X]

end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic) (n h k : ℕ)
    (hn : p.natDegree=n) (hh : 1 ≤ h) (hhk : h ≤ k) (hk : k ≤ n-2)
    (A : ℂ) (Q : Polynomial ℂ) (hQ : Q.natDegree < h)
    (hgap : centeredSource p=X^n+C A*X^k+Q)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ R) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧
      chainCost z ≤ Real.sqrt (h+1)*Real.sqrt (R^2-‖rootCentroid p‖^2) ∧
      (A=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (R^2-‖rootCentroid p‖^2)) := by
  let c := appellCoefficients (centeredSource p)
  have hq : 2 ≤ n-k := by omega
  have hqM : n-k ≤ n-h := by omega
  have hc0 : c 0=1 := appellCoefficients_zero _ (centeredSource_monic p hp)
  have hcoef (j : ℕ) (hj : j ≤ n-h) (hj0 : j ≠ 0) (hjq : j ≠ n-k) : c j=0 := by
    dsimp only [c,appellCoefficients]
    rw [centeredSource_natDegree,hn,hgap,coeff_add,coeff_add]
    have hQ0 : Q.coeff (n-j)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [coeff_X_pow,coeff_C_mul,hQ0]
    rw [if_neg (by omega : n-j ≠ n),if_neg (by omega : n-j ≠ k)]
    simp
  have hsrc : translatedAppell n c (rootCentroid p)=p := by
    simpa only [translatedAppell,hn,c] using translatedAppell_centeredSource p
  have hsum : n-h+h=n := by omega
  have hdisk (z : ℂ) (hz : (translatedAppell (n-h+h) c (rootCentroid p)).eval z=0) : ‖z‖ ≤ R := by
    rw [hsum,hsrc] at hz
    exact hbound z hz
  have hresult : ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧
      chainCost z ≤ Real.sqrt (h+1)*Real.sqrt (R^2-‖rootCentroid p‖^2) ∧
      (c (n-k)=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (R^2-‖rootCentroid p‖^2)) := by
    obtain ⟨z,hzr,hz0,hzc,hzz⟩ := sparse_appell_chain_bound (n-h) h (n-k) hq hqM
      c hc0 hcoef (rootCentroid p) R hR hdisk
    let w : Fin n → ℂ := fun i => z (Fin.cast hsum.symm i)
    have hwcost : chainCost w=chainCost z := chainCost_cast_index hsum.symm z
    refine ⟨w,?_,?_,?_,?_⟩
    · intro i
      simpa only [w,Fin.val_cast,hsum,hsrc] using hzr (Fin.cast hsum.symm i)
    · exact hz0
    · rwa [hwcost]
    · intro hh
      rw [hwcost]
      exact hzz hh
  obtain ⟨w,hwroot,hwstart,hwcost,hwzero⟩ := hresult
  refine ⟨w,hwroot,hwstart,hwcost,?_⟩
  intro hA
  apply hwzero
  dsimp only [c,appellCoefficients]
  rw [centeredSource_natDegree,hn,show n-(n-k)=k by omega,hgap,hA]
  have hQ0 : Q.coeff k=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hQ0,show k ≠ n by omega]
