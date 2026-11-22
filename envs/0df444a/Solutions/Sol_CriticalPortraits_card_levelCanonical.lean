-- Prove2me | solution 1 for CriticalPortraits.card_levelCanonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:50.038064+00:00
-- url     : https://prove2.me/submissions/3c00dcd9-e926-4adb-afe1-d90ed4ff264c

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Theorems.Thm_CriticalPortraits_card_levelCanonical_mul

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
open _root_.CriticalPortraits.Cycle
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Fintype.card {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}
      = (d * m).choose (d - 1) / d :=
  (Nat.div_eq_of_eq_mul_right hd (card_levelCanonical_mul d m hd hm).symm).symm
end CriticalPortraits
