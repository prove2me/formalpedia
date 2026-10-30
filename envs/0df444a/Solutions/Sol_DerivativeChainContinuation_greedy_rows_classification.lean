-- Prove2me | solution 1 for DerivativeChainContinuation.greedy_rows_classification
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:44:26.489988+00:00
-- url     : https://prove2.me/submissions/3e642b8d-c7e1-44ba-adcc-f817bb7a9019

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_first_derivative_unique_nearest
import Theorems.Thm_DerivativeChainContinuation_last_derivative_unique_nearest
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
open Polynomial
open scoped BigOperators




















theorem greedy_right_step (r : RealRows) (k : ℕ)
    (hmono : ∀ j≤k+2, Monotone (r j)) (hstep : RealRowStep r (k+1))
    (v : ℝ) (hv : ∃ i : Fin (k+3),v=r (k+2) i)
    (hnear : ∀ i : Fin (k+3), |v-rightRow r (k+1)|≤|r (k+2) i-rightRow r (k+1)|) :
    v=rightRow r (k+2) := by
  obtain ⟨i,rfl⟩ := hv
  by_contra hi
  have h := last_derivative_unique_nearest k (r (k+2)) (r (k+1))
    (hmono _ le_rfl) (hmono _ (by omega)) hstep.1 (by simpa only [Nat.cast_add,Nat.cast_one,
      (show (k : ℝ)+1+2=(k : ℝ)+3 from by ring)] using hstep.2) i hi
  exact (not_lt_of_ge (hnear (Fin.last (k+2)))) h

theorem greedy_left_step (r : RealRows) (k : ℕ)
    (hmono : ∀ j≤k+2, Monotone (r j)) (hstep : RealRowStep r (k+1))
    (v : ℝ) (hv : ∃ i : Fin (k+3),v=r (k+2) i)
    (hnear : ∀ i : Fin (k+3), |v-leftRow r (k+1)|≤|r (k+2) i-leftRow r (k+1)|) :
    v=leftRow r (k+2) := by
  obtain ⟨i,rfl⟩ := hv
  by_contra hi
  have h := first_derivative_unique_nearest k (r (k+2)) (r (k+1))
    (hmono _ le_rfl) (hmono _ (by omega)) hstep.1 (by simpa only [Nat.cast_add,Nat.cast_one,
      (show (k : ℝ)+1+2=(k : ℝ)+3 from by ring)] using hstep.2) i hi
  exact (not_lt_of_ge (hnear 0)) h

theorem greedy_follows_right (r : RealRows) (n : ℕ) (x : ℕ → ℝ)
    (hmono : ∀ j≤n, Monotone (r j)) (hstep : ∀ j<n, RealRowStep r j)
    (hx : GreedyRowsTo r n x) (hfirst : x 1=rightRow r 1) :
    ∀ k≤n, 1≤k → x k=rightRow r k := by
  intro k hk hpos
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => exact hfirst
  | more k ih0 ih1 =>
    have he := ih1 (by omega) (by omega)
    apply greedy_right_step r k (fun j hj => hmono j (by omega))
      (hstep (k+1) (by omega)) _ (hx.1 (k+2) hk)
    intro i
    simpa only [he] using hx.2 (k+1) (by omega) i

theorem greedy_follows_left (r : RealRows) (n : ℕ) (x : ℕ → ℝ)
    (hmono : ∀ j≤n, Monotone (r j)) (hstep : ∀ j<n, RealRowStep r j)
    (hx : GreedyRowsTo r n x) (hfirst : x 1=leftRow r 1) :
    ∀ k≤n, 1≤k → x k=leftRow r k := by
  intro k hk hpos
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => exact hfirst
  | more k ih0 ih1 =>
    have he := ih1 (by omega) (by omega)
    apply greedy_left_step r k (fun j hj => hmono j (by omega))
      (hstep (k+1) (by omega)) _ (hx.1 (k+2) hk)
    intro i
    simpa only [he] using hx.2 (k+1) (by omega) i




end DerivativeChainContinuation

theorem solution (r : RealRows) (n : ℕ) (hn : 1≤n)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j)
    (x : ℕ → ℝ) (hx : GreedyRowsTo r n x) :
    (∀ k≤n,x k=leftRow r k) ∨ (∀ k≤n,x k=rightRow r k) := by
  have hzero : x 0=r 0 0 := by
    obtain ⟨j,hj⟩ := hx.1 0 (by omega)
    rw [Fin.eq_zero j] at hj
    exact hj
  obtain ⟨j,hj⟩ := hx.1 1 hn
  fin_cases j
  · left
    intro k hk
    by_cases he : k=0
    · subst k; exact hzero
    · exact greedy_follows_left r n x hmono hstep hx hj k hk (by omega)
  · right
    intro k hk
    by_cases he : k=0
    · subst k; exact hzero
    · exact greedy_follows_right r n x hmono hstep hx hj k hk (by omega)
