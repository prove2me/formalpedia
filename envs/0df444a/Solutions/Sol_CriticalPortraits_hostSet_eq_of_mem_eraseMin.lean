-- Prove2me | solution 1 for CriticalPortraits.hostSet_eq_of_mem_eraseMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:00.914907+00:00
-- url     : https://prove2.me/submissions/badad8e9-27a1-4bf7-9781-570a50b6c260

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
public import Theorems.Thm_CriticalPortraits_mem_T


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
    {S : Finset (ZMod (d * m))} (hS : S ∈ P) {x : ZMod (d * m)} (hxe : x ∈ eraseMin S) :
    hostSet P x (mem_T.mpr ⟨S, hS, hxe⟩) = S := by
  set hx : x ∈ T P := mem_T.mpr ⟨S, hS, hxe⟩ with hhx
  by_contra hne
  -- both S and hostSet P x hx contain x; if distinct they are disjoint — contradiction.
  have hhost : hostSet P x hx ∈ P := hostSet_mem hx
  have hxS : x ∈ S := eraseMin_subset S hxe
  have hxH : x ∈ hostSet P x hx := mem_hostSet hx
  have hdisj := hP.2.1 _ hhost _ hS (by exact fun h => hne h)
  exact (Finset.disjoint_left.mp hdisj hxH) hxS
end CriticalPortraits
