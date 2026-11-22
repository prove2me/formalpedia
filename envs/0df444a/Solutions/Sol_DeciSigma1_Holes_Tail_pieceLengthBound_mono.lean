-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.pieceLengthBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:46.198941+00:00
-- url     : https://prove2.me/submissions/58e616a5-ce6a-44e9-820b-c4c243180f3b

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {N d d' h t : ℕ} (hd : d ≤ d') :
    pieceLengthBound N d h t ≤ pieceLengthBound N d' h t := by
  unfold pieceLengthBound fixedMargin comparisonGap boundaryMargin stateTransientLength
    statePeriodModulus
  have h2 := Nat.mul_le_mul_right N.factorial hd
  have h3 := Nat.mul_le_mul_left N hd
  have h4 := Nat.mul_le_mul_left ((t + 1) * 2 ^ h - 1)
    (show 2 * (N * d + d * N.factorial) + d * N.factorial + d * N.factorial ≤
      2 * (N * d' + d' * N.factorial) + d' * N.factorial + d' * N.factorial by omega)
  omega
end DeciSigma1.Holes.Tail
