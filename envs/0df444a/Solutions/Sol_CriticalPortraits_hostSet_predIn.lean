-- Prove2me | solution 1 for CriticalPortraits.hostSet_predIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:43.182255+00:00
-- url     : https://prove2.me/submissions/aacfcdf5-a49a-4d5f-bb63-0700748bc7dd

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
public import Theorems.Thm_CriticalPortraits_hostSet_eq_of_mem

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
theorem _root_.solution [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u : ZMod (d * m)} (hu : u ∈ T P) (hpu : predIn P u hu ∈ T P) :
    hostSet P (predIn P u hu) hpu = hostSet P u hu :=
  hostSet_eq_of_mem hP hpu (hostSet_mem hu) (predIn_mem_host hu)
end CriticalPortraits
