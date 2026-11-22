-- Prove2me | solution 1 for CriticalPortraits.column_sep_geom_dir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:11.185609+00:00
-- url     : https://prove2.me/submissions/4a5e133c-9ee5-4d38-aa91-a65d9f7fb6f6

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
public import Theorems.Thm_AbstractLaminar_column_sep_with_gap
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
    ∃ g, loV P e < g ∧ g ≤ hiV e ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        ¬ (loV P r < g ∧ g ≤ hiV r)) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        hiV r < g → colV e < colV r) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        g ≤ loV P r → colV r < colV e) := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := edge_tight_geom hd hm hP he
  have heE : e ∈ fam.E := he
  exact AbstractLaminar.column_sep_with_gap fam hwin hsat heE rfl rfl
end CriticalPortraits
