-- Prove2me | solution 1 for CriticalPortraits.level_lt_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:53.192776+00:00
-- url     : https://prove2.me/submissions/2a4815bd-645d-4d56-830f-810217d3e004

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
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (_hm : 0 < m) (x : ZMod (d * m)) [NeZero (d * m)] : x.val / m < d := by
  have hlt : x.val < d * m := ZMod.val_lt x
  have hdiv : (x.val / m) * m ≤ x.val := Nat.div_mul_le_self x.val m
  by_contra hge
  push Not at hge
  have : d * m ≤ (x.val / m) * m := Nat.mul_le_mul_right m hge
  omega
end CriticalPortraits
