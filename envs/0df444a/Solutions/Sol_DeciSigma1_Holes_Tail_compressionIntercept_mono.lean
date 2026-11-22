-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.compressionIntercept_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:24.307608+00:00
-- url     : https://prove2.me/submissions/a0a961df-eada-47f5-ba37-9b64f67265b0

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
theorem _root_.solution (k N D : ℕ) : Monotone (compressionIntercept k N D) := by
  intro r s h
  unfold compressionIntercept
  gcongr
end DeciSigma1.Holes.Tail
