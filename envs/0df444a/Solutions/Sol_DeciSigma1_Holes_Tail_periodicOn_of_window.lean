-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.periodicOn_of_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:57.056359+00:00
-- url     : https://prove2.me/submissions/ee9aa283-389b-4fe4-893e-fff05a6ec3d8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {w : List α} {p g s e a b : ℕ} (hp : PeriodicOn w p s e)
    (hg : PeriodicOn w g a b)
    (hsa : s ≤ a) (hbe : b ≤ e) (hlen : a + p + g ≤ b) (hp0 : 0 < p) : PeriodicOn w g s e := by
  intro x hx hxe
  set y := a + (x + p * a - a) % p with hy
  have hya : a ≤ y := Nat.le_add_right _ _
  have hyp : y < a + p := by have := Nat.mod_lt (x + p * a - a) hp0; omega
  have hmod : y % p = x % p := by
    have h1 : a ≤ p * a := Nat.le_mul_of_pos_left a hp0
    have e1 : y ≡ a + (x + p * a - a) [MOD p] := Nat.ModEq.add_left a (Nat.mod_modEq _ _)
    have e2 : a + (x + p * a - a) = x + p * a := by omega
    rw [e2] at e1
    have e3 : x + p * a ≡ x [MOD p] := by
      unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
    exact e1.trans e3
  have hmod' : (y + g) % p = (x + g) % p := by rw [Nat.add_mod, hmod, ← Nat.add_mod]
  rw [hp.eq_of_mod hx (by omega) (by omega) (by omega) hmod.symm, hg y hya (by omega),
    hp.eq_of_mod (by omega) (by omega) (by omega) (by omega) hmod']
end DeciSigma1.Holes.Tail
