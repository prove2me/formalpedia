-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.markerTypes_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:53.320329+00:00
-- url     : https://prove2.me/submissions/7f46077c-8d4b-48b5-969e-b9d8a1736637

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_eq_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {r : ℕ} (u : List α) (c : ℕ) : (markerTypes W r u c).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨m, hm, hs, rfl⟩ := mem_markerTypes.mp hx
  obtain ⟨m', hm', hs', rfl⟩ := mem_markerTypes.mp hy
  exact marker_eq_of_suffix hm hm' hs hs'
end DeciSigma1.Holes.Fresh
