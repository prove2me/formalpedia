-- Prove2me | solution 1 for CriticalPortraits.hostSet_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:04.250181+00:00
-- url     : https://prove2.me/submissions/78647aca-4399-4a04-87d7-9c97a7aca1a1

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u : ZMod (d * m)} (hu : u ∈ T P) {S : Finset (ZMod (d * m))} (hSP : S ∈ P) (huS : u ∈ S) :
    hostSet P u hu = S := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hP.2.1 _ (hostSet_mem hu) _ hSP hne) (mem_hostSet hu)) huS
end CriticalPortraits
