-- Prove2me | solution 1 for CriticalPortraits.betaBlock_critical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:19.878029+00:00
-- url     : https://prove2.me/submissions/2b093c19-13b9-4716-9050-bb7a0e425a9e

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
public import Theorems.Thm_CriticalPortraits_betaBlock_sameFiber
public import Theorems.Thm_CriticalPortraits_betaBlock_two_le

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {v : ZMod (d * m)}
    (hv : v ∈ bVerts U) : IsCriticalSet d m (betaBlock U v) := by
  have : NeZero (d*m) := ⟨by positivity⟩
  refine ⟨⟨v.val % m, Nat.mod_lt _ hm, ?_⟩, betaBlock_two_le hd hm hcanon hv⟩
  intro y hy
  exact betaBlock_sameFiber hd hm hcanon hy
end CriticalPortraits
