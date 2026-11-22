-- Prove2me | solution 1 for CriticalPortraits.exists_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:41.351386+00:00
-- url     : https://prove2.me/submissions/4111cc4c-fd41-42cf-aeaf-1f43b72b9087

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
public import Theorems.Thm_CriticalPortraits_discrete_ivt
public import Theorems.Thm_CriticalPortraits_Defc_step
public import Theorems.Thm_CriticalPortraits_Defc_top_nonneg
public import Theorems.Thm_CriticalPortraits_Defc_bot_nonpos

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    ∃ k ≤ u.val / m - 1, Defc U (u.val % m) (u.val / m) u.val k = 0 := by
  apply discrete_ivt (fun k => Defc U (u.val % m) (u.val / m) u.val k) (u.val / m - 1)
  · exact Defc_bot_nonpos hd hm hcanon hu hlu
  · exact Defc_top_nonneg U (u.val % m) (u.val / m) u.val hlu
  · intro k _
    exact Defc_step hm U (u.val % m) (u.val / m) u.val k
end CriticalPortraits
