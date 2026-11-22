-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_suffix_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:15.882597+00:00
-- url     : https://prove2.me/submissions/7c810d30-ff4f-44e2-9769-343b98db873a

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix_succ
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {r t : ℕ} (hrt : r ≤ t)
    {m : Fin k} (hm : m ∈ active W t) : marker W r m <:+ marker W t m := by
  induction t, hrt using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ t _ ih =>
    exact (ih (active_succ_subset W t hm)).trans (marker_suffix_succ hm)
end DeciSigma1.Holes.Fresh
