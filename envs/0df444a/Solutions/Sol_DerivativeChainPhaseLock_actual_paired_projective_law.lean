-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_paired_projective_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:17:23.240501+00:00
-- url     : https://prove2.me/submissions/b0b59aff-d283-4ac3-8c17-d925d4a8fa61

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_ProjectiveHistories
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


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







theorem appellRow_derivative (m : ℕ) (c : ℕ → ℂ) :
    (appellRow (m+1) c).derivative = C (m+1:ℂ)*appellRow m c := by
  ext k
  rw [coeff_derivative,coeff_C_mul,appellRow_coeff_eq,appellRow_coeff_eq]
  have hch : (m+1:ℂ)*(m.choose k:ℂ) = ((m+1).choose (k+1):ℂ)*(k+1:ℂ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m k
  rw [show m+1-(k+1)=m-k by omega]
  push_cast
  linear_combination -c (m-k)*hch

theorem appellRow_iterate_derivative (m k : ℕ) (c : ℕ → ℂ) :
    derivative^[k] (appellRow (m+k) c) = C ((m+k).descFactorial k:ℂ)*appellRow m c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m+Nat.succ k=(m+k)+1 by omega,Function.iterate_succ_apply,
      appellRow_derivative,iterate_derivative_C_mul,ih,← mul_assoc,← C_mul]
    rw [Nat.succ_descFactorial_succ]
    push_cast
    rfl

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





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



end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPhaseLock
noncomputable section

theorem appell_eval_neg (m : ℕ) (c : ℕ → ℂ) (hc : ∀ j, Odd j → c j=0) (z : ℂ) :
    (appellRow m c).eval (-z)=(-1:ℂ)^m*(appellRow m c).eval z := by
  simp only [appellRow,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rcases Nat.even_or_odd (m-k) with he | ho
  · have hsign : (-1:ℂ)^k=(-1:ℂ)^m := by
      have h := congrArg (fun j : ℕ => (-1:ℂ)^j) (Nat.sub_add_cancel hkm)
      simpa only [pow_add,he.neg_one_pow,one_mul] using h
    have hneg : (-z)^k=(-1:ℂ)^k*z^k := by rw [neg_eq_neg_one_mul,mul_pow]
    rw [hneg,hsign]
    ring
  · simp only [hc (m-k) ho,mul_zero,zero_mul]

theorem actual_appell_eval_neg (N m : ℕ) (c : ℕ → ℂ) (hm : m ≤ N)
    (hc : ∀ j, Odd j → c j=0) (z : ℂ) :
    ((derivative^[N-m]) (appellRow N c)).eval (-z)=
      (-1:ℂ)^m*((derivative^[N-m]) (appellRow N c)).eval z := by
  have h := appellRow_iterate_derivative m (N-m) c
  rw [Nat.add_sub_of_le hm] at h
  rw [h,eval_mul,eval_C,eval_mul,eval_C,appell_eval_neg m c hc]
  ring

theorem actual_polynomial_eval_neg (p : Polynomial ℂ) (m : ℕ) (hm : m ≤ p.natDegree)
    (hc : ∀ j, Odd j → appellCoefficients p j=0) (z : ℂ) :
    ((derivative^[p.natDegree-m]) p).eval (-z)=
      (-1:ℂ)^m*((derivative^[p.natDegree-m]) p).eval z := by
  have h := actual_appell_eval_neg p.natDegree m (appellCoefficients p) hm hc z
  simpa only [appellRow_coefficients] using h

theorem actual_row_root_neg {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (m : ℕ) (hm : m ≤ n+1) (z : ℂ) (hz : (row a m).eval z=0) :
    (row a m).eval (-z)=0 := by
  have hd : (fromRoots a).natDegree=n+1 := by
    unfold fromRoots
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hp := actual_polynomial_eval_neg (fromRoots a) m (by rwa [hd]) hc z
  simp only [row] at hz ⊢
  simpa only [hd,hz,mul_zero] using hp

theorem actual_chain_neg {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (z : Fin (n+1) → ℂ) (hz : IsChain a z) : IsChain a (fun i => -z i) := by
  intro i
  exact actual_row_root_neg a hc (i.val+1) (by omega) (z i) (hz i)

theorem chainCost_neg {n : ℕ} (z : Fin n → ℂ) :
    chainCost (fun i => -z i)=chainCost z := by
  unfold chainCost
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_sub_neg,norm_sub_rev]

end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section






theorem projectiveStep_neg_left (x y : ℂ) : projectiveStep (-x) y=projectiveStep x y := by
  simp only [projectiveStep,sub_eq_add_neg,neg_neg,add_comm,min_comm]

theorem projectiveOrient_sign (x : ℕ → ℂ) (k : ℕ) :
    projectiveOrient x k=x k ∨ projectiveOrient x k= -x k := by
  cases k with
  | zero => exact Or.inl rfl
  | succ k => dsimp only [projectiveOrient]; split_ifs <;> simp

theorem projectiveOrient_norm (x : ℕ → ℂ) (k : ℕ) : ‖projectiveOrient x k‖=‖x k‖ := by
  rcases projectiveOrient_sign x k with h | h <;> rw [h] <;> simp

theorem projectiveOrient_step (x : ℕ → ℂ) (k : ℕ) :
    ‖projectiveOrient x (k+1)-projectiveOrient x k‖=projectiveStep (x k) (x (k+1)) := by
  have hcost : ‖projectiveOrient x (k+1)-projectiveOrient x k‖=
      projectiveStep (projectiveOrient x k) (x (k+1)) := by
    rw [projectiveOrient]
    split_ifs with h
    · exact (min_eq_left h).symm
    · change ‖-x (k+1)-projectiveOrient x k‖=
        min ‖x (k+1)-projectiveOrient x k‖ ‖x (k+1)+projectiveOrient x k‖
      rw [show -x (k+1)-projectiveOrient x k= -(x (k+1)+projectiveOrient x k) by ring,
        norm_neg,min_eq_right (le_of_lt (lt_of_not_ge h))]
  rcases projectiveOrient_sign x k with h | h
  · simpa only [h] using hcost
  · simpa only [h,projectiveStep_neg_left] using hcost

theorem projective_history_cost (x : ℕ → ℂ) (n : ℕ) :
    chainCost (projectiveHistory x n)=projectivePathLength x n := by
  change (∑ i : Fin n, ‖projectiveOrient x (i.val+1)-projectiveOrient x i.val‖)=
    ∑ k∈Finset.range n,projectiveStep (x k) (x (k+1))
  simp_rw [projectiveOrient_step]
  exact Fin.sum_univ_eq_sum_range (fun k => projectiveStep (x k) (x (k+1))) n

theorem actual_projective_history {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : IsChain a (fun i => x i.val)) :
    IsChain a (projectiveHistory x n) := by
  intro i
  rcases projectiveOrient_sign x i.val with h | h
  · simpa only [projectiveHistory,h] using hx i
  · change (row a (i.val+1)).eval (projectiveOrient x i.val)=0
    rw [h]
    exact actual_row_root_neg a hc (i.val+1) (by omega) (x i.val) (hx i)



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
open DerivativeChainPhaseLock



















theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → _root_.DerivativeChainContinuation.appellCoefficients (_root_.DerivativeChainPrivate.fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : _root_.DerivativeChainPrivate.IsChain a (fun i => x i.val)) (hx0 : x 0=0) :
    ∃ L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a 0 (Fin 2),
      (∀ i,L.weights i=1/2) ∧ L.paths 0=_root_.DerivativeChainPhaseLock.projectiveHistory x n ∧
      L.paths 1=(fun i => -_root_.DerivativeChainPhaseLock.projectiveHistory x n i) ∧
      (∀ i,_root_.DerivativeChainPrivate.chainCost (L.paths i)=_root_.DerivativeChainPhaseLock.projectivePathLength x n) ∧
      L.endpointVariance=‖x n‖^2 ∧ L.meanSquareCost=(_root_.DerivativeChainPhaseLock.projectivePathLength x n)^2 := by
  let z := _root_.DerivativeChainPhaseLock.projectiveHistory x n
  have hz : _root_.DerivativeChainPrivate.IsChain a z := _root_.DerivativeChainPhaseLock.actual_projective_history a hc x hx
  have hz0 : z 0=0 := hx0
  let L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a 0 (Fin 2) := {
    weights := fun _ => 1/2
    nonneg := by intro i; norm_num
    total := by norm_num
    paths := ![z,fun i => -z i]
    actual := by intro i; fin_cases i; exact hz; exact _root_.DerivativeChainPhaseLock.actual_chain_neg a hc z hz
    start := by
      intro i
      fin_cases i
      · exact hz0
      · change -z 0=0
        rw [hz0,neg_zero]
    balanced := by norm_num [Fin.sum_univ_succ] }
  have hw (i : Fin 2) : L.weights i=1/2 := rfl
  have hcst (i : Fin 2) : _root_.DerivativeChainPrivate.chainCost (L.paths i)=_root_.DerivativeChainPhaseLock.projectivePathLength x n := by
    fin_cases i
    · exact _root_.DerivativeChainPhaseLock.projective_history_cost x n
    · change _root_.DerivativeChainPrivate.chainCost (fun i => -z i)=_root_.DerivativeChainPhaseLock.projectivePathLength x n
      rw [_root_.DerivativeChainPhaseLock.chainCost_neg]
      exact _root_.DerivativeChainPhaseLock.projective_history_cost x n
  have hnorm : ‖z (Fin.last n)‖=‖x n‖ := _root_.DerivativeChainPhaseLock.projectiveOrient_norm x n
  have hvar : L.endpointVariance=‖x n‖^2 := by
    change (∑ i : Fin 2, (1/2:ℝ)*‖(![z,fun j => -z j] i) (Fin.last n)-0‖^2)=‖x n‖^2
    norm_num [Fin.sum_univ_succ,hnorm]
    ring
  have hcost : L.meanSquareCost=(_root_.DerivativeChainPhaseLock.projectivePathLength x n)^2 := by
    change (∑ i,L.weights i*_root_.DerivativeChainPrivate.chainCost (L.paths i)^2)=(_root_.DerivativeChainPhaseLock.projectivePathLength x n)^2
    simp_rw [hcst]
    rw [← Finset.sum_mul,L.total,one_mul]
  exact ⟨L,hw,rfl,rfl,hcst,hvar,hcost⟩
