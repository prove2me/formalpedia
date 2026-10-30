-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_greedy_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:49:21.266332+00:00
-- url     : https://prove2.me/submissions/af5a9dec-fcfb-480f-9b77-cb14a6049408

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_maximal_child_unique_nearest
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_rows_before_activation
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













theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem actual_complex_row_natDegree {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) : (row a m).natDegree=m := by
  rw [row,complex_iterate_derivative_natDegree,actual_complex_source_natDegree]
  omega













theorem actual_ordinary_row_derivative {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hmn : m ≤ n) : (row a (m+1)).derivative=row a m := by
  unfold row
  rw [show n+1-m=(n+1-(m+1))+1 by omega,Function.iterate_succ_apply']

theorem positive_actual_high_row_class {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (m : ℕ) (hm : k ≤ m) (hmn : m ≤ n+1) :
    ∃ s : ℕ, ∃ V : Polynomial ℝ,PositiveQuotient V ∧ 0<V.natDegree ∧ row a m=spokePoly k s V := by
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  obtain ⟨s,V,hV,hVdegree,heq⟩ := positive_spoke_rows_before_activation n k r Q hk hQ hQdegree hd
    (n+1-m) (by omega)
  exact ⟨s,V,hV,hVdegree,by simpa only [row,hp] using heq⟩






end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem complexHistoryOf_val {n : ℕ} (z : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    complexHistoryOf z i.val=z i := by simp [complexHistoryOf,i.isLt]

theorem complexHistoryOf_root {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hz : DerivativeChainPrivate.IsChain a z) (j : ℕ) (hj : j ≤ n) :
    (row a (j+1)).eval (complexHistoryOf z j)=0 := by
  simpa only [complexHistoryOf,dif_pos (show j<n+1 by omega)] using hz ⟨j,by omega⟩

theorem complexHistoryOf_nearest {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hz : IsGreedyChain a z) (j : ℕ) (hj : j<n) (w : ℂ)
    (hw : (row a (j+2)).eval w=0) :
    ‖complexHistoryOf z (j+1)-complexHistoryOf z j‖ ≤ ‖w-complexHistoryOf z j‖ := by
  have h := hz.2 ⟨j,hj⟩ w hw
  rw [←complexHistoryOf_val z (⟨j,hj⟩ : Fin n).succ,
    ←complexHistoryOf_val z (⟨j,hj⟩ : Fin n).castSucc] at h
  simpa only [Fin.val_succ,Fin.val_castSucc,Fin.val_mk] using h









end DerivativeChainContinuation

theorem solution {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (hz : IsGreedyChain a z) (m : ℕ) (hm : k ≤ m) (hmn : m ≤ n)
    (hw : complexHistoryOf z (m-1)≠0)
    (hmax : ∀ w : ℂ,(row a m).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z (m-1)‖) :
    complexHistoryOf z m≠0 ∧
      (∀ w : ℂ,(row a (m+1)).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z m‖) ∧
      ∃ c : ℝ,1 ≤ c ∧ complexHistoryOf z m=(c : ℂ)*complexHistoryOf z (m-1) := by
  obtain ⟨s,V,hV,hVdegree,heq⟩ := positive_actual_high_row_class a k r Q hk hQ hQdegree hp
    (m+1) (by omega) (by omega)
  have hder : (spokePoly k s V).derivative=row a m := by
    rw [←heq]
    exact actual_ordinary_row_derivative a m hmn
  have hdegree : 2 ≤ (spokePoly k s V).natDegree := by
    rw [←heq,actual_complex_row_natDegree a (m+1) (by omega) (by omega)]
    omega
  have hchild : (spokePoly k s V).derivative.eval (complexHistoryOf z (m-1))=0 := by
    rw [hder]
    have h := complexHistoryOf_root a z hz.1 (m-1) (by omega)
    rwa [show m-1+1=m by omega] at h
  obtain ⟨v,hvroot,hwv,⟨c,hc,hvform⟩,hvmax,hvnear⟩ :=
    positive_spoke_maximal_child_unique_nearest k s V hk hV hVdegree hdegree
      (complexHistoryOf z (m-1)) hw hchild (by simpa only [hder] using hmax)
  have hactualv : (row a (m+1)).eval v=0 := by rwa [heq]
  have hnear := complexHistoryOf_nearest a z hz (m-1) (by omega) v (by
    simpa only [show m-1+2=m+1 by omega] using hactualv)
  rw [show m-1+1=m by omega] at hnear
  have hselectedroot : (spokePoly k s V).eval (complexHistoryOf z m)=0 := by
    rw [←heq]
    exact complexHistoryOf_root a z hz.1 m hmn
  have hselected : complexHistoryOf z m=v := (hvnear _ hselectedroot).2 hnear
  have hvnonzero : v≠0 := by
    intro hv0
    rw [hv0,norm_zero] at hwv
    have hwpos := norm_pos_iff.mpr hw
    linarith
  refine ⟨by rwa [hselected],?_,⟨c,hc,by rw [hselected,hvform]⟩⟩
  intro w hwroot
  rw [hselected]
  exact hvmax w (by rwa [←heq])
