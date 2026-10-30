-- Prove2me | solution 1 for DerivativeChainContinuation.single_centered_mode_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:14:12.842279+00:00
-- url     : https://prove2.me/submissions/fb89cb67-a8ce-4364-b858-72382998fafc

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
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
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic) (n q : ℕ)
    (hn : p.natDegree=n) (hq : 2 ≤ q) (hqn : q ≤ n)
    (hsupport : ∀ j ≤ n, 2 ≤ j → j ≠ q → (centeredSource p).coeff (n-j)=0)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ chainCost z ≤ Real.sqrt (D^2-‖rootCentroid p-a‖^2) ∧
      ((centeredSource p).coeff (n-q)=0 → chainCost z=0) := by
  let c := appellCoefficients (centeredSource p)
  have hc0 : c 0=1 := appellCoefficients_zero _ (centeredSource_monic p hp)
  have hc1 : c 1=0 := appellCoefficients_one _ (centeredSource_monic p hp)
    (by rw [centeredSource_natDegree,hn]; omega) (centeredSource_centered p (by omega))
  have hc (j : ℕ) (hz : (centeredSource p).coeff (n-j)=0) : c j=0 := by
    dsimp only [c,appellCoefficients]
    rw [centeredSource_natDegree,hn,hz,zero_div]
  have hpref (j : ℕ) (hj : j ≤ n) (hj0 : j ≠ 0) (hjq : j ≠ q) : c j=0 := by
    by_cases hj1 : j=1
    · subst j; exact hc1
    · exact hc j (hsupport j hj (by omega) hjq)
  have hsrc : translatedAppell n c (rootCentroid p)=p := by
    simpa only [translatedAppell,hn,c] using translatedAppell_centeredSource p
  have hdisk (w : ℂ) (hw : (translatedAppell (n+0) c (rootCentroid p)).eval w=0) : ‖w-a‖ ≤ D := by
    rw [Nat.add_zero,hsrc] at hw
    exact hbound w hw
  obtain ⟨z,hzr,hz0,hzc,hzz⟩ := appell_no_return_disk_bound n 0 q hq hqn c hc0 hpref
    (rootCentroid p) a D hD hdisk
  refine ⟨z,?_,hz0,?_,?_⟩
  · simpa only [Nat.add_zero,hsrc] using hzr
  · simpa using hzc
  · intro hz
    have hh : chainCost z ≤ 0 := by simpa using hzz (hc q hz)
    exact le_antisymm hh (by unfold chainCost; positivity)
