-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.splitPieceLengthBound_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:23.746379+00:00
-- url     : https://prove2.me/submissions/5ddb0d9f-34af-4707-bf0b-204f5d100fe8

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (k N D r E : ℕ) :
    Periodic.pieceLengthBound N D (k * (N - 1)) (2 * r + E) =
      compressionIntercept k N D r + compressionSlope k N D * E := by
  have hQ : 1 ≤ 2 ^ (k * (N - 1)) := Nat.one_le_pow _ _ (by decide)
  have hbase : 1 ≤ (2 * r + 1) * 2 ^ (k * (N - 1)) := by nlinarith
  unfold Periodic.pieceLengthBound compressionIntercept compressionSlope
  rw [show (2 * r + E + 1) * 2 ^ (k * (N - 1)) =
    E * 2 ^ (k * (N - 1)) + (2 * r + 1) * 2 ^ (k * (N - 1)) by ring,
    Nat.add_sub_assoc hbase]
  ring
end DeciSigma1.Holes.Tail
