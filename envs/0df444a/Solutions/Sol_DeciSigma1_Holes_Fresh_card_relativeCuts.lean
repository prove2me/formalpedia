-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_relativeCuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:20.580113+00:00
-- url     : https://prove2.me/submissions/0434922d-62f7-4ab0-8424-7a62e9311622

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A : Finset ℕ) (s e : ℕ) :
    (relativeCuts A s e).card = anchorCount A s e := by
  unfold relativeCuts anchorCount
  apply card_image_iff.mpr
  intro a ha b hb heq
  change a - s = b - s at heq
  have ha' := (Finset.mem_filter.mp ha).2.1
  have hb' := (Finset.mem_filter.mp hb).2.1
  omega
end DeciSigma1.Holes.Fresh
