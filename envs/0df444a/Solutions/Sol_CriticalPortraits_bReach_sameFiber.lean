-- Prove2me | solution 1 for CriticalPortraits.bReach_sameFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:08.365694+00:00
-- url     : https://prove2.me/submissions/bbba97b2-119d-431a-9d80-f8cccf774a49

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_bAdj_sameFiber

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {a b : ZMod (d * m)} (h : bReach U a b) :
    a.val % m = b.val % m := by
  unfold bReach at h
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih => rw [ih]; exact bAdj_sameFiber hd hm hcanon hxy
end CriticalPortraits
