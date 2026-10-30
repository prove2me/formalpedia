-- Prove2me | solution 1 for DerivativeChainContinuation.real_greedy_half_span
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:01:21.557642+00:00
-- url     : https://prove2.me/submissions/bcf8bc19-010a-4c1c-bc89-bf6e5a2ee15c

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_GreedyTower
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_real_row_root_iff
import Theorems.Thm_DerivativeChainContinuation_left_rows_greedy
import Theorems.Thm_DerivativeChainContinuation_real_tower_exists
import Theorems.Thm_DerivativeChainContinuation_right_rows_greedy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem real_source_map {n : ℕ} (a : Fin (n+1) → ℝ) :
    fromRoots (fun i => (a i : ℂ))=(realRootProduct a).map Complex.ofRealHom := by
  simp only [fromRoots,realRootProduct,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,Complex.ofRealHom_eq_coe]











theorem real_history_actual_greedy (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (x : ℕ → ℝ) (hx : GreedyRowsTo r n x) :
    IsGreedyChain (fun i => (r n i : ℂ)) (fun i => (x i.val : ℂ)) := by
  constructor
  · intro i
    obtain ⟨j,hj⟩ := hx.1 i.val (by omega)
    exact (actual_real_row_root_iff r n hstep i.val (by omega) _).mpr
      ⟨j,by change (x i.val : ℂ)=(r i.val j : ℂ); rw [hj]⟩
  · intro i w hw
    obtain ⟨j,rfl⟩ := (actual_real_row_root_iff r n hstep (i.val+1) (by omega) w).mp hw
    simpa only [Fin.val_succ,Fin.val_castSucc,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs] using hx.2 i.val i.isLt j

theorem real_history_actual_cost (n : ℕ) (x : ℕ → ℝ) :
    chainCost (fun i : Fin (n+1) => (x i.val : ℂ))=greedyCost x n := by
  unfold chainCost greedyCost
  change (∑ i : Fin n,‖(x (i.val+1) : ℂ)-(x i.val : ℂ)‖)=_
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact Fin.sum_univ_eq_sum_range (fun k => |x (k+1)-x k|) n







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_reindex {n : ℕ} (a : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    realRootProduct (a ∘ e)=realRootProduct a := by
  exact Equiv.prod_comp e (fun i => X-C (a i))










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem orderedSource_mono {n : ℕ} (a : Fin (n+1) → ℝ) : Monotone (orderedSource a) :=
  Tuple.monotone_sort a



theorem orderedSource_fromRoots {n : ℕ} (a : Fin (n+1) → ℝ) :
    fromRoots (fun i => (a i : ℂ))=
      fromRoots (fun i => (orderedSource a i : ℂ)) := by
  rw [real_source_map,real_source_map]
  unfold orderedSource
  rw [realRootProduct_reindex]

theorem orderedSource_greedy_iff {n : ℕ} (a : Fin (n+1) → ℝ)
    (z : Fin (n+1) → ℂ) :
    IsGreedyChain (fun i => (a i : ℂ)) z ↔
      IsGreedyChain (fun i => (orderedSource a i : ℂ)) z := by
  simp only [IsGreedyChain,DerivativeChainPrivate.IsChain,row,orderedSource_fromRoots a]















end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





theorem tower_right_step (r : RealRows) (k : ℕ) (hstep : RealRowStep r k) :
    rightRow r k≤rightRow r (k+1) := by
  simpa using (hstep.1 (Fin.last k)).2

theorem tower_left_step (r : RealRows) (k : ℕ) (hstep : RealRowStep r k) :
    leftRow r (k+1)≤leftRow r k := by
  simpa using (hstep.1 0).1

theorem tower_right_cost (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) :
    greedyCost (rightRow r) n=rightRow r n-r 0 0 := by
  induction n with
  | zero => simp [greedyCost,rightRow]
  | succ n ih =>
    have hi := ih (fun k hk => hstep k (by omega))
    unfold greedyCost at hi ⊢
    rw [Finset.sum_range_succ,hi,abs_of_nonneg
      (sub_nonneg.mpr (tower_right_step r n (hstep n (by omega))))]
    ring

theorem tower_left_cost (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) :
    greedyCost (leftRow r) n=r 0 0-leftRow r n := by
  induction n with
  | zero => simp [greedyCost,leftRow]
  | succ n ih =>
    have hi := ih (fun k hk => hstep k (by omega))
    unfold greedyCost at hi ⊢
    rw [Finset.sum_range_succ,hi,abs_of_nonpos
      (sub_nonpos.mpr (tower_left_step r n (hstep n (by omega))))]
    ring













theorem greedy_rows_half_span (r : RealRows) (n : ℕ)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j) :
    ∃ x : ℕ → ℝ, GreedyRowsTo r n x ∧
      greedyCost x n≤(rightRow r n-leftRow r n)/2 := by
  by_cases h : r 0 0-leftRow r n≤rightRow r n-r 0 0
  · refine ⟨leftRow r,left_rows_greedy r n hmono hstep,?_⟩
    rw [tower_left_cost r n hstep]
    linarith
  · refine ⟨rightRow r,right_rows_greedy r n hmono hstep,?_⟩
    rw [tower_right_cost r n hstep]
    linarith






end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+1) → ℝ) :
    ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z≤(orderedSource a (Fin.last n)-orderedSource a 0)/2 := by
  obtain ⟨r,hr,hm,hs⟩ := real_tower_exists n (orderedSource a) (orderedSource_mono a)
  obtain ⟨x,hx,hc⟩ := greedy_rows_half_span r n hm hs
  let z : Fin (n+1) → ℂ := fun i => (x i.val : ℂ)
  have hz : IsGreedyChain (fun i => (orderedSource a i : ℂ)) z := by
    simpa only [hr] using real_history_actual_greedy r n hs x hx
  refine ⟨z,(orderedSource_greedy_iff a z).mpr hz,?_⟩
  rw [show z=(fun i => (x i.val : ℂ)) from rfl,real_history_actual_cost]
  simpa only [rightRow,leftRow,hr] using hc
