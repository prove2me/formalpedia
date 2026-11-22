-- Prove2me | solution 1 for CriticalPortraits.T_surjOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:05.149968+00:00
-- url     : https://prove2.me/submissions/8fd382fe-2ae8-45d7-aa18-1a05dd67c795

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_T_beta
public import Theorems.Thm_CriticalPortraits_beta_portrait

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Set.SurjOn (T (N := d*m)) {P | Portrait d m P}
      {U | U.card = d - 1 ∧ LevelCanonical d m U} := by
  intro U hU
  exact ⟨beta U, beta_portrait hd hm hU.1 hU.2, T_beta hd hm hU.2⟩
end CriticalPortraits
