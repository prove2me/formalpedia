-- Prove2me | solution 1 for CriticalPortraits.edge_tight_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:58.203037+00:00
-- url     : https://prove2.me/submissions/ecc86986-b6af-4fc7-9039-858610ba26ed

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
public import Theorems.Thm_AbstractLaminar_edge_tight_of_saturated
public import Theorems.Thm_CriticalPortraits_survivorFamily_contained_eq
public import Theorems.Thm_CriticalPortraits_survivorFamily_saturated

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
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) :
    AbstractLaminar.N (survivorFamily hd hm hP) (loV P e) (hiV e)
      = hiV e - loV P e := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := survivorFamily_saturated hd hm hP
  have hcont : e ∈ AbstractLaminar.contained fam 0 (d - 1) := by
    rw [survivorFamily_contained_eq hd hm hP]; exact he
  have := AbstractLaminar.edge_tight_of_saturated fam (d - 1 - 0) 0 (d - 1) rfl hsat e hcont
  exact this
end CriticalPortraits
