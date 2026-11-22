-- Prove2me | solution 1 for CriticalPortraits.beta_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:36.869061+00:00
-- url     : https://prove2.me/submissions/3f2f9953-8a52-40a5-a406-613ffe5483af

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
public import Theorems.Thm_CriticalPortraits_betaBlock_disjoint

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Disjoint A B := by
  intro A hA B hB hAB
  rw [mem_beta_iff] at hA hB
  obtain ⟨v1, _, hA1⟩ := hA
  obtain ⟨v2, _, hB1⟩ := hB
  subst hA1; subst hB1
  exact betaBlock_disjoint hAB
end CriticalPortraits
