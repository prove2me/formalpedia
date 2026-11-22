-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.expansionBlockCountBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:29.548619+00:00
-- url     : https://prove2.me/submissions/0b64d007-f9c4-4664-a698-c5accb849c9a

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
theorem _root_.solution (k n : ℕ) : 0 < expansionBlockCountBound k n := by
  unfold expansionBlockCountBound edgeLengthBound
  exact Nat.mul_pos (by omega) (by omega)
end DeciSigma1.Holes.Fresh
