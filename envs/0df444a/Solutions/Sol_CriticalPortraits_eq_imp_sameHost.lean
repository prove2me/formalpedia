-- Prove2me | solution 1 for CriticalPortraits.eq_imp_sameHost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:49.487414+00:00
-- url     : https://prove2.me/submissions/5aa72a05-1b2a-40b2-be76-8b5f7d35eb6d

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P) (hxy : x = y) :
    hostSet P x hx = hostSet P y hy := by
  by_contra hne
  have hdisj := hP.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hne
  have hmemx : x ∈ hostSet P x hx := mem_hostSet hx
  have hmemy : x ∈ hostSet P y hy := hxy ▸ mem_hostSet hy
  exact (Finset.disjoint_left.mp hdisj hmemx) hmemy
end CriticalPortraits
