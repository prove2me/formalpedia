-- Prove2me | solution 1 for CriticalPortraits.sameblock_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.119918+00:00
-- url     : https://prove2.me/submissions/055cd334-7965-4223-8c65-ecb3e5872a27

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
public import Theorems.Thm_CriticalPortraits_val_decomp
public import Theorems.Thm_CriticalPortraits_sep_master


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N m : ℕ} (hm : 0 < m) {x y : ZMod N}
    (ha : x.val / m < y.val / m) : x.val < y.val := by
  have hp : x.val % m < m := Nat.mod_lt _ hm
  have hq : y.val % m < m := Nat.mod_lt _ hm
  have hx := val_decomp (m := m) x; have hy := val_decomp (m := m) y
  have := sep_master (m := m) (p := x.val % m) (q := y.val % m)
      (a := x.val / m) (c := y.val / m) hp hq ha
  omega
end CriticalPortraits
