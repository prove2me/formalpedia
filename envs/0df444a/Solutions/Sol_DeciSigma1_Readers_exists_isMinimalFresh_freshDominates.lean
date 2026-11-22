-- Prove2me | solution 1 for DeciSigma1.Readers.exists_isMinimalFresh_freshDominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:46.023062+00:00
-- url     : https://prove2.me/submissions/c1cd2e10-c852-4850-9bbd-78f8f7a3db96

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Theorems.Thm_DeciSigma1_Readers_Dominates_refl
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_refl
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
variable [DecidableEq α] [DecidableEq S]
variable {T : Table α S k} {U V W : Fin k → List α}
namespace DeciSigma1.Readers
theorem _root_.solution (hW : ∀ i, T.Fresh W i) :
    ∃ U, FreshDominates T U W ∧ IsMinimalFresh T U := by
  classical
  have hex : ∃ n, ∃ U, FreshDominates T U W ∧ totalLength U = n :=
      ⟨_, W, FreshDominates.refl hW, rfl⟩
  obtain ⟨U, hU, hn⟩ := Nat.find_spec hex
  refine ⟨U, hU, hU.2, fun V hV => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨V, hV.trans hU, rfl⟩
end DeciSigma1.Readers
