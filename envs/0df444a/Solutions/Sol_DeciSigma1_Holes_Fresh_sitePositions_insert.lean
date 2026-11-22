-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.sitePositions_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:22.573803+00:00
-- url     : https://prove2.me/submissions/c7b98ea7-963f-42ce-b830-86722a967b09

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (c : ℕ) (cs : Finset ℕ) :
    sitePositions δ (insert c cs) = sitePositions δ cs ∪ Finset.Ico c (c + δ) := by
  rw [sitePositions, Finset.biUnion_insert, Finset.union_comm]; rfl
end DeciSigma1.Holes.Fresh
