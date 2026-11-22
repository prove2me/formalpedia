-- Prove2me | solution 1 for CriticalPortraits.column_sep_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:23.539661+00:00
-- url     : https://prove2.me/submissions/1f4ac485-e503-46e8-9617-5c9004f43162

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
public import Theorems.Thm_AbstractLaminar_column_sep
public import Theorems.Thm_CriticalPortraits_edge_tight_geom

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
    {e : ZMod (d * m)} (he : e ∈ T P) (hwin : loV P e < hiV e) :
    ∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
      colV r ≠ colV e := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := edge_tight_geom hd hm hP he
  -- `e` itself is the top edge of window (loV e, hiV e].
  have heE : e ∈ fam.E := he
  exact AbstractLaminar.column_sep fam hwin hsat heE rfl rfl
end CriticalPortraits
