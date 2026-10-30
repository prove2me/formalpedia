-- Prove2me | solution 1 for DerivativeChainContinuation.actual_real_greedy_classification
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:53:40.611561+00:00
-- url     : https://prove2.me/submissions/4fb4f2fa-afe3-468e-8aef-1ccef04b96e7

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyTower
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_real_row_root_iff
import Theorems.Thm_DerivativeChainContinuation_greedy_rows_classification
import Theorems.Thm_DerivativeChainContinuation_left_rows_greedy
import Theorems.Thm_DerivativeChainContinuation_real_tower_exists
import Theorems.Thm_DerivativeChainContinuation_right_rows_greedy
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









theorem realHistoryOf_val {n : ℕ} (z : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    realHistoryOf z i.val=(z i).re := by simp [realHistoryOf,i.isLt]

theorem actual_greedy_real_history (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (z : Fin (n+1) → ℂ)
    (hz : IsGreedyChain (fun i => (r n i : ℂ)) z) :
    (∀ i,z i=(realHistoryOf z i.val : ℂ)) ∧
      GreedyRowsTo r n (realHistoryOf z) := by
  have hroot (i : Fin (n+1)) : ∃ j : Fin (i.val+1),z i=(r i.val j : ℂ) :=
    (actual_real_row_root_iff r n hstep i.val (by omega) (z i)).mp (hz.1 i)
  have hreal (i : Fin (n+1)) : z i=(realHistoryOf z i.val : ℂ) := by
    rw [realHistoryOf_val]
    obtain ⟨j,hj⟩ := hroot i
    rw [hj]
    simp
  refine ⟨hreal,?_,?_⟩
  · intro k hk
    obtain ⟨j,hj⟩ := hroot ⟨k,by omega⟩
    refine ⟨j,?_⟩
    simpa [realHistoryOf,show k<n+1 by omega] using congrArg Complex.re hj
  · intro k hk j
    have hp : (row (fun i => (r n i : ℂ)) (k+2)).eval (r (k+1) j : ℂ)=0 :=
      (actual_real_row_root_iff r n hstep (k+1) (by omega) _).mpr ⟨j,rfl⟩
    have h := hz.2 ⟨k,hk⟩ (r (k+1) j : ℂ) hp
    rw [hreal (⟨k,hk⟩ : Fin n).succ,hreal (⟨k,hk⟩ : Fin n).castSucc] at h
    simpa only [Fin.val_succ,Fin.val_castSucc,Fin.val_mk,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem actual_chain_cost_eq {n : ℕ} (z : Fin (n+1) → ℂ)
    (hreal : ∀ i,z i=(realHistoryOf z i.val : ℂ)) :
    chainCost z=greedyCost (realHistoryOf z) n := by
  unfold chainCost greedyCost
  change (∑ i : Fin n,‖z i.succ-z i.castSucc‖)=_
  simp_rw [hreal,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact Fin.sum_univ_eq_sum_range (fun k => |realHistoryOf z (k+1)-realHistoryOf z k|) n

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









theorem greedyCost_congr (x y : ℕ → ℝ) (n : ℕ)
    (h : ∀ k≤n,x k=y k) : greedyCost x n=greedyCost y n := by
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [h (k+1) (by omega),h k (by omega)]

theorem greedy_rows_exact_cost (r : RealRows) (n : ℕ) (hn : 1≤n)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j)
    (x : ℕ → ℝ) (hx : GreedyRowsTo r n x) :
    ((∀ k≤n,x k=leftRow r k) ∧ greedyCost x n=r 0 0-leftRow r n) ∨
    ((∀ k≤n,x k=rightRow r k) ∧ greedyCost x n=rightRow r n-r 0 0) := by
  rcases greedy_rows_classification r n hn hmono hstep x hx with hl | hr
  · exact Or.inl ⟨hl,(greedyCost_congr x _ n hl).trans (tower_left_cost r n hstep)⟩
  · exact Or.inr ⟨hr,(greedyCost_congr x _ n hr).trans (tower_right_cost r n hstep)⟩

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

theorem solution (n : ℕ) (hn : 1≤n)
    (a : Fin (n+1) → ℝ) (ha : Monotone a) :
    ∃ r : RealRows, r n=a ∧
      (∀ k≤n,Monotone (r k)) ∧ (∀ k<n,RealRowStep r k) ∧
      (∀ k≤n,∀ w : ℂ,
        (row (fun i => (a i : ℂ)) (k+1)).eval w=0 ↔
          ∃ j : Fin (k+1),w=(r k j : ℂ)) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ↔
        (∀ i,z i=(leftRow r i.val : ℂ)) ∨
        (∀ i,z i=(rightRow r i.val : ℂ))) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z →
        chainCost z=realCentroid a-a 0 ∨
        chainCost z=a (Fin.last n)-realCentroid a) ∧
      (∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
        chainCost z≤(a (Fin.last n)-a 0)/2) := by
  obtain ⟨r,hr,hm,hs⟩ := real_tower_exists n a ha
  have hc : r 0 0=realCentroid a := by
    have h := tower_centroid r n hs
    rw [hr] at h
    unfold realCentroid
    rw [h]
    have hn' : (n+1 : ℝ)≠0 := by positivity
    field_simp
  refine ⟨r,hr,hm,hs,?_,?_,?_,?_⟩
  · intro k hk w
    simpa only [hr] using actual_real_row_root_iff r n hs k hk w
  · intro z
    constructor
    · intro hz
      have hz' : IsGreedyChain (fun i => (r n i : ℂ)) z := by simpa only [hr] using hz
      obtain ⟨hzr,hg⟩ := actual_greedy_real_history r n hs z hz'
      rcases greedy_rows_classification r n hn hm hs _ hg with hl | hrr
      · left
        intro i
        rw [hzr i,hl i.val (by omega)]
      · right
        intro i
        rw [hzr i,hrr i.val (by omega)]
    · rintro (hl | hrr)
      · have he : z=(fun i => (leftRow r i.val : ℂ)) := funext hl
        rw [he]
        simpa only [hr] using real_history_actual_greedy r n hs _ (left_rows_greedy r n hm hs)
      · have he : z=(fun i => (rightRow r i.val : ℂ)) := funext hrr
        rw [he]
        simpa only [hr] using real_history_actual_greedy r n hs _ (right_rows_greedy r n hm hs)
  · intro z hz
    have hz' : IsGreedyChain (fun i => (r n i : ℂ)) z := by simpa only [hr] using hz
    obtain ⟨hzr,hg⟩ := actual_greedy_real_history r n hs z hz'
    rw [actual_chain_cost_eq z hzr]
    rcases greedy_rows_exact_cost r n hn hm hs _ hg with hl | hrr
    · exact Or.inl (by simpa only [hc,leftRow,hr] using hl.2)
    · exact Or.inr (by simpa only [hc,rightRow,hr] using hrr.2)
  · obtain ⟨x,hx,hcost⟩ := greedy_rows_half_span r n hm hs
    refine ⟨fun i => (x i.val : ℂ),?_,?_⟩
    · simpa only [hr] using real_history_actual_greedy r n hs x hx
    · rw [real_history_actual_cost]
      simpa only [rightRow,leftRow,hr] using hcost
