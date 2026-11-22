-- Prove2me | solution 1 for CriticalPortraits.bReach_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:07.509597+00:00
-- url     : https://prove2.me/submissions/a3c125e1-7956-4454-9f89-86f0b24142ea

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
theorem _root_.solution {U : Finset (ZMod (d * m))} {a b c : ZMod (d * m)}
    (h1 : bReach U a b) (h2 : bReach U b c) : bReach U a c :=
  Relation.ReflTransGen.trans h1 h2
end CriticalPortraits
