-- Prove2me | solution 1 for CriticalPortraits.betaK_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:38.969032+00:00
-- url     : https://prove2.me/submissions/b208aa47-5b94-470d-8090-f253e9964baf

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

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {s : ZMod (d * m)} {k : ℕ}
    (hk : Defc U (s.val % m) (s.val / m) s.val k = 0) (hkle : k ≤ s.val / m - 1) :
    k ≤ betaK U s := by
  classical
  exact Nat.le_findGreatest hkle hk
end CriticalPortraits
