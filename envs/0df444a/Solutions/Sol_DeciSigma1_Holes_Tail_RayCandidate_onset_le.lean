-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.RayCandidate.onset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:57:55.102154+00:00
-- url     : https://prove2.me/submissions/7f7b2a98-b148-406a-8048-af4d1806c8fa

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Holes_Tail_onset_repeatFactorRay_le


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Holes.Tail.RayCandidate
variable [DecidableEq α] {M : StructuralReader α S k} {W : Fin k → List α} {ts : List (List α)}
  {v : Fin k}
namespace DeciSigma1.Holes.Tail.RayCandidate
theorem _root_.solution (x : RayCandidate M W ts v) : x.ray.onset ≤ x.startCut :=
  onset_repeatFactorRay_le _ _
end DeciSigma1.Holes.Tail.RayCandidate
