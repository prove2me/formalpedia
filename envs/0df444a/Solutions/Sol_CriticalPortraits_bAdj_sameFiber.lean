-- Prove2me | solution 1 for CriticalPortraits.bAdj_sameFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:30.626413+00:00
-- url     : https://prove2.me/submissions/f75ea0af-769d-4330-8006-ad49a43134ab

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
public import Theorems.Thm_CriticalPortraits_betaParent_fiber

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (_hcanon : LevelCanonical d m U) {a b : ZMod (d * m)} (h : bAdj U a b) :
    a.val % m = b.val % m := by
  rcases h with ⟨hbU, hblu, hab⟩ | ⟨haU, halu, hba⟩
  · rw [hab]; exact betaParent_fiber hd hm hblu
  · rw [hba]; exact (betaParent_fiber hd hm halu).symm
end CriticalPortraits
