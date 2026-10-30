-- Prove2me | solution 1 for DerivativeChainContinuation.real_tower_exists
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:37:11.593124+00:00
-- url     : https://prove2.me/submissions/d7feeab2-945f-4fc7-a3e5-08ed8f1563be

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_derivative_interlacing
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℝ) (ha : Monotone a) :
    ∃ r : RealRows, r n=a ∧ (∀ k ≤ n, Monotone (r k)) ∧ (∀ k<n, RealRowStep r k) := by
  classical
  induction n with
  | zero =>
    let r : RealRows := fun _ _ => a 0
    refine ⟨r,?_,?_,?_⟩
    · funext i
      have hi : i=0 := Fin.eq_zero i
      simp [r,hi]
    · intro k hk i j hij
      rfl
    · intro k hk
      omega
  | succ n ih =>
    obtain ⟨b,hbmono,hbinter,hbderiv⟩ := real_derivative_interlacing n a ha
    obtain ⟨r,hrtop,hrmono,hrstep⟩ := ih b hbmono
    let rr : RealRows := Function.update r (n+1) a
    have hrr (k : ℕ) (hk : k ≤ n) : rr k = r k := by
      simp [rr,Function.update_of_ne (show k ≠ n+1 by omega)]
    have htop : rr (n+1) = a := by simp [rr]
    refine ⟨rr,htop,?_,?_⟩
    · intro k hk
      by_cases he : k=n+1
      · subst k
        rw [htop]
        exact ha
      · rw [hrr k (by omega)]
        exact hrmono k (by omega)
    · intro k hk
      by_cases he : k=n
      · subst k
        simp only [RealRowStep,htop,hrr n le_rfl,hrtop]
        exact ⟨hbinter,hbderiv⟩
      · simp only [RealRowStep,hrr k (by omega),hrr (k+1) (by omega)]
        exact hrstep k (by omega)
