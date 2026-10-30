-- Prove2me | solution 1 for DerivativeChainContinuation.sparse_cluster_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:02:15.383409+00:00
-- url     : https://prove2.me/submissions/7412f2fc-55ea-4344-81c8-6fcb3c50c7e1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appell_centroid_return_bound
import Theorems.Thm_DerivativeChainContinuation_appell_no_return_disk_bound
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem centeredSource_roots (p : Polynomial ℂ) :
    (centeredSource p).roots = p.roots.map (fun z => z-rootCentroid p) := by
  simpa [centeredSource] using
    (roots_comp_C_mul_X_add_C p 1 (rootCentroid p) isUnit_one)

theorem centeredSource_natDegree (p : Polynomial ℂ) :
    (centeredSource p).natDegree = p.natDegree := by
  rw [centeredSource, natDegree_comp, natDegree_X_add_C, mul_one]

theorem centeredSource_monic (p : Polynomial ℂ) (hp : p.Monic) :
    (centeredSource p).Monic := hp.comp_X_add_C _

theorem centeredSource_centered (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (centeredSource p).roots.sum = 0 := by
  rw [centeredSource_roots]
  have hc := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnC : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast hn
  simp [Multiset.sum_map_sub, hc, rootCentroid, nsmul_eq_mul]
  field_simp [hnC]
  ring




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
namespace DerivativeChainContinuation
open Polynomial

theorem appellCoefficients_one (p : Polynomial ℂ) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hc : p.roots.sum=0) : appellCoefficients p 1=0 := by
  have ht := (IsAlgClosed.splits p).nextCoeff_eq_neg_sum_roots_of_monic hp
  rw [hc,neg_zero,nextCoeff_of_natDegree_pos hn] at ht
  simp only [appellCoefficients,ht,zero_div]

end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n r h q : ℕ) (hn : p.natDegree=n) (hh : 1 ≤ h)
    (hq : 2 ≤ q) (hqr : q ≤ r-h) (hrn : r ≤ n)
    (hsupport : ∀ j ≤ n, 2 ≤ j → j ≠ q → (j ≤ r-h ∨ r < j) →
      (centeredSource p).coeff (n-j)=0)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ (∀ i, r ≤ i.val → z i=rootCentroid p) ∧
      chainCost z ≤ ((if r=n then 0 else 1)+Real.sqrt (h+1 : ℕ))*Real.sqrt (D^2-‖rootCentroid p-a‖^2) ∧
      ((centeredSource p).coeff (n-q)=0 →
        chainCost z ≤ ((if r=n then 0 else 1)+Real.sqrt h)*Real.sqrt (D^2-‖rootCentroid p-a‖^2)) := by
  let c := appellCoefficients (centeredSource p)
  have hc0 : c 0=1 := appellCoefficients_zero _ (centeredSource_monic p hp)
  have hc1 : c 1=0 := appellCoefficients_one _ (centeredSource_monic p hp)
    (by rw [centeredSource_natDegree,hn]; omega) (centeredSource_centered p (by omega))
  have hconvert (j : ℕ) (hz : (centeredSource p).coeff (n-j)=0) : c j=0 := by
    dsimp only [c,appellCoefficients]
    rw [centeredSource_natDegree,hn,hz,zero_div]
  have hpref (j : ℕ) (hj : j ≤ r-h) (hj0 : j ≠ 0) (hjq : j ≠ q) : c j=0 := by
    by_cases hj1 : j=1
    · subst j; exact hc1
    · exact hconvert j (hsupport j (by omega) (by omega) hjq (Or.inl hj))
  have hupper (j : ℕ) (hjr : r < j) (hjn : j ≤ n) : c j=0 :=
    hconvert j (hsupport j hjn (by omega) (by omega) (Or.inr hjr))
  have hsrc : translatedAppell n c (rootCentroid p)=p := by
    simpa only [translatedAppell,hn,c] using translatedAppell_centeredSource p
  by_cases hr : r=n
  · subst r
    simp only [if_pos rfl,ite_true,zero_add]
    have hsum : n-h+h=n := by omega
    have hdisk (w : ℂ) (hw : (translatedAppell (n-h+h) c (rootCentroid p)).eval w=0) : ‖w-a‖ ≤ D := by
      rw [hsum,hsrc] at hw; exact hbound w hw
    obtain ⟨z,hzr,hz0,hzc,hzz⟩ := appell_no_return_disk_bound (n-h) h q hq hqr c hc0 hpref
      (rootCentroid p) a D hD hdisk
    let v : Fin n → ℂ := fun i => z (Fin.cast hsum.symm i)
    have hcost : chainCost v=chainCost z := chainCost_cast_index hsum.symm z
    refine ⟨v,?_,hz0,?_,?_,?_⟩
    · intro i
      simpa only [v,Fin.val_cast,hsum,hsrc] using hzr (Fin.cast hsum.symm i)
    · intro i hi; omega
    · rwa [hcost]
    · intro hz; rw [hcost]; exact hzz (hconvert q hz)
  · simp only [if_neg hr]
    have hMH : r-h+h=r := by omega
    have hsum : r-h+h+(n-r)=n := by omega
    have hdisk (w : ℂ) (hw : (translatedAppell (r-h+h+(n-r)) c (rootCentroid p)).eval w=0) : ‖w-a‖ ≤ D := by
      rw [hsum,hsrc] at hw; exact hbound w hw
    have hret (j : ℕ) (hj : r-h+h < j) (hj' : j ≤ r-h+h+(n-r)) : c j=0 :=
      hupper j (by omega) (by omega)
    obtain ⟨z,hzr,hz0,hzt,hzc,hzz⟩ := appell_centroid_return_bound (r-h) h (n-r) q hq hqr
      (by omega) c hc0 hpref hret (rootCentroid p) a D hD hdisk
    let v : Fin n → ℂ := fun i => z (Fin.cast hsum.symm i)
    have hcost : chainCost v=chainCost z := chainCost_cast_index hsum.symm z
    refine ⟨v,?_,hz0,?_,?_,?_⟩
    · intro i
      simpa only [v,Fin.val_cast,hsum,hsrc] using hzr (Fin.cast hsum.symm i)
    · intro i hi
      exact hzt (Fin.cast hsum.symm i) (by simpa only [Fin.val_cast,hMH] using hi)
    · rwa [hcost]
    · intro hz; rw [hcost]; exact hzz (hconvert q hz)
