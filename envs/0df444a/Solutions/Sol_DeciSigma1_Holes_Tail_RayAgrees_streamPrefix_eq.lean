-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.RayAgrees.streamPrefix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:40.999847+00:00
-- url     : https://prove2.me/submissions/fc02aa8e-a11f-4c3d-b7aa-512b85990c0f

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace RayAgrees
theorem _root_.solution {Ω : Ray α} {x : List α} {E a : ℕ} (h : RayAgrees Ω x E)
    (ha : a ≤ E) : streamPrefix Ω.stream a = x.take a := by
  have := congrArg (List.take a) h.2
  rw [take_streamPrefix, List.take_take, min_eq_left ha] at this
  exact this
end RayAgrees
end DeciSigma1.Holes.Tail
