-- Prove2me | solution 1 for CriticalPortraits.betaBlock_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:01.351742+00:00
-- url     : https://prove2.me/submissions/e3691184-c88c-42cf-a146-3985fb5d4348

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
public import Theorems.Thm_CriticalPortraits_bReach_symm
public import Theorems.Thm_CriticalPortraits_bReach_trans
public import Theorems.Thm_CriticalPortraits_betaBlock_eq_of_bReach

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {v1 v2 : ZMod (d * m)}
    (hne : betaBlock U v1 ≠ betaBlock U v2) : Disjoint (betaBlock U v1) (betaBlock U v2) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  rw [mem_betaBlock] at hz1 hz2
  obtain ⟨_, hr1⟩ := hz1
  obtain ⟨_, hr2⟩ := hz2
  -- v1 reaches z, v2 reaches z ⇒ v1 reaches v2 ⇒ blocks equal
  have hv12 : bReach U v1 v2 := bReach_trans hr1 (bReach_symm hr2)
  exact hne (betaBlock_eq_of_bReach hv12)
end CriticalPortraits
