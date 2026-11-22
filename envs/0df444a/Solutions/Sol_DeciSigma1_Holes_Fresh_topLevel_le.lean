-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.topLevel_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:46.476825+00:00
-- url     : https://prove2.me/submissions/f36ab6c0-0cad-4621-a15c-2473c2c69e52

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_nonempty_of_le_topLevel
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixOccurrenceCuts_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_card_prefixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i) :
    topLevel W ≤ k * (Fintype.card S - 1) := by
  rcases Nat.eq_zero_or_pos (topLevel W) with h0 | hpos
  · omega
  · obtain ⟨l, hl⟩ := active_nonempty_of_le_topLevel (W := W) hpos le_rfl
    exact (le_card_prefixOccurrenceCuts hpos l hl).trans (card_prefixOccurrenceCuts_le hfr _)
end DeciSigma1.Holes.Fresh
