-- Prove2me | solution 1 for CriticalPortraits.betaK_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:17.054489+00:00
-- url     : https://prove2.me/submissions/5396f0e8-16cb-49fe-b5f7-4f71cc26c8d4

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
public import Theorems.Thm_CriticalPortraits_exists_balance

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
    Defc U (u.val % m) (u.val / m) u.val (betaK U u) = 0 := by
  classical
  obtain ⟨k, hkle, hkdef⟩ := exists_balance hd hm hcanon hu hlu
  have := Nat.findGreatest_spec (P := fun k => Defc U (u.val % m) (u.val / m) u.val k = 0)
    (m := k) (n := u.val / m - 1) hkle hkdef
  exact this
end CriticalPortraits
