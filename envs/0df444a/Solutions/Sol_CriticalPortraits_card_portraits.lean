-- Prove2me | solution 1 for CriticalPortraits.card_portraits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:41:50.473377+00:00
-- url     : https://prove2.me/submissions/f17867bf-fb29-4c51-87b3-64558b94cc89

module
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Census
public import Theorems.Thm_CriticalPortraits_card_portraits_mul

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) / d :=
  (Nat.div_eq_of_eq_mul_right hd (card_portraits_mul hd hm).symm).symm
end CriticalPortraits
