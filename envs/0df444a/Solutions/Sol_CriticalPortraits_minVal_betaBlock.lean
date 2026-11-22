-- Prove2me | solution 1 for CriticalPortraits.minVal_betaBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:14.834588+00:00
-- url     : https://prove2.me/submissions/d360b99c-f05d-4d32-8efa-2f5d24a52f13

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
public import Theorems.Thm_CriticalPortraits_betaRoot_mem_block
public import Theorems.Thm_CriticalPortraits_betaRoot_min_in_block
public import Theorems.Thm_CriticalPortraits_minVal_le


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) :
    minVal (betaBlock U x) (betaBlock_nonempty hx) = betaRoot hd hm hcanon x := by
  have : NeZero (d*m) := ⟨by positivity⟩
  set h := betaBlock_nonempty hx
  -- minVal ≤ root.val and root.val ≤ minVal.val (root is min)
  have h1 : (minVal (betaBlock U x) h).val ≤ (betaRoot hd hm hcanon x).val :=
    minVal_le (betaBlock U x) h _ (betaRoot_mem_block hd hm hcanon hx)
  have h2 : (betaRoot hd hm hcanon x).val ≤ (minVal (betaBlock U x) h).val :=
    betaRoot_min_in_block hd hm hcanon (minVal_mem (betaBlock U x) h)
  exact ZMod.val_injective _ (le_antisymm h1 h2)
end CriticalPortraits
