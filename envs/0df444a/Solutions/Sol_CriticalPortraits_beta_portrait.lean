-- Prove2me | solution 1 for CriticalPortraits.beta_portrait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:38:30.942425+00:00
-- url     : https://prove2.me/submissions/f70db5f9-e39f-4b4b-9147-0414321bb739

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
public import Theorems.Thm_CriticalPortraits_mem_beta_iff
public import Theorems.Thm_CriticalPortraits_betaBlock_critical
public import Theorems.Thm_CriticalPortraits_beta_pairwise_disjoint
public import Theorems.Thm_CriticalPortraits_beta_weight
public import Theorems.Thm_CriticalPortraits_beta_unlinked

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcard : U.card = d - 1) (hcanon : LevelCanonical d m U) : Portrait d m (beta U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsCriticalSet
    intro S hS
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    exact betaBlock_critical hd hm hcanon hv
  · -- Disjoint
    exact beta_pairwise_disjoint
  · -- Unlinked
    exact beta_unlinked hd hm hcanon
  · -- weight
    exact beta_weight hd hm hcard hcanon
end CriticalPortraits
