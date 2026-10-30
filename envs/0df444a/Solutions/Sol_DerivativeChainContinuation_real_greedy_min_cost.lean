-- Prove2me | solution 1 for DerivativeChainContinuation.real_greedy_min_cost
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:03:38.208389+00:00
-- url     : https://prove2.me/submissions/ae8cadaa-c356-453d-a533-57c736b5796a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_GreedyTower
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_greedy_all_histories
import Theorems.Thm_DerivativeChainContinuation_tower_centroid
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

















theorem real_history_actual_cost (n : ℕ) (x : ℕ → ℝ) :
    chainCost (fun i : Fin (n+1) => (x i.val : ℂ))=greedyCost x n := by
  unfold chainCost greedyCost
  change (∑ i : Fin n,‖(x (i.val+1) : ℂ)-(x i.val : ℂ)‖)=_
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact Fin.sum_univ_eq_sum_range (fun k => |x (k+1)-x k|) n







end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators











theorem orderedSource_centroid {n : ℕ} (a : Fin (n+1) → ℝ) :
    realCentroid (orderedSource a)=realCentroid a := by
  unfold realCentroid orderedSource
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (Tuple.sort a) a]













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




















end DerivativeChainContinuation

theorem solution (n : ℕ) (hn : 1≤n) (a : Fin (n+1) → ℝ) :
    ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z=min (realCentroid a-orderedSource a 0)
        (orderedSource a (Fin.last n)-realCentroid a) ∧
      (∀ w : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) w →
        chainCost z≤chainCost w) ∧
      chainCost z≤(orderedSource a (Fin.last n)-orderedSource a 0)/2 := by
  obtain ⟨r,hr,hm,hs,hrows,hclass,hcost,hex⟩ := real_greedy_all_histories n hn a
  have hcentroid : r 0 0=realCentroid a := by
    have h := tower_centroid r n hs
    rw [hr] at h
    have h' : realCentroid (orderedSource a)=r 0 0 := by
      unfold realCentroid
      rw [h]
      have hn' : (n+1 : ℝ)≠0 := by positivity
      field_simp
    rw [orderedSource_centroid] at h'
    exact h'.symm
  have hleft : ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z=realCentroid a-orderedSource a 0 := by
    refine ⟨fun i => (leftRow r i.val : ℂ),(hclass _).mpr (Or.inl (fun i => rfl)),?_⟩
    rw [real_history_actual_cost,tower_left_cost r n hs]
    rw [hcentroid]
    change realCentroid a-r n 0=_
    rw [hr]
  have hright : ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z=orderedSource a (Fin.last n)-realCentroid a := by
    refine ⟨fun i => (rightRow r i.val : ℂ),(hclass _).mpr (Or.inr (fun i => rfl)),?_⟩
    rw [real_history_actual_cost,tower_right_cost r n hs]
    rw [hcentroid]
    change r n (Fin.last n)-realCentroid a=_
    rw [hr]
  have he : ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z=min (realCentroid a-orderedSource a 0)
        (orderedSource a (Fin.last n)-realCentroid a) := by
    by_cases h : realCentroid a-orderedSource a 0≤orderedSource a (Fin.last n)-realCentroid a
    · obtain ⟨z,hz,hc⟩ := hleft
      exact ⟨z,hz,hc.trans (min_eq_left h).symm⟩
    · obtain ⟨z,hz,hc⟩ := hright
      exact ⟨z,hz,hc.trans (min_eq_right (le_of_not_ge h)).symm⟩
  obtain ⟨z,hz,hzmin⟩ := he
  refine ⟨z,hz,hzmin,?_,?_⟩
  · intro w hw
    rw [hzmin]
    rcases hcost w hw with hl | hrr
    · rw [hl]; exact min_le_left _ _
    · rw [hrr]; exact min_le_right _ _
  · rw [hzmin]
    have hl := min_le_left (realCentroid a-orderedSource a 0)
      (orderedSource a (Fin.last n)-realCentroid a)
    have hrr := min_le_right (realCentroid a-orderedSource a 0)
      (orderedSource a (Fin.last n)-realCentroid a)
    linarith
