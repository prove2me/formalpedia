-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.RayAgrees.stream_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:40.068451+00:00
-- url     : https://prove2.me/submissions/ce1049d9-4c18-43e5-8829-1a980ad41204

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_RayAgrees_getElem__ac7111bad97d
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace RayAgrees
theorem _root_.solution {Ω Ω' : Ray α} {x : List α} {E E' t : ℕ} (h : RayAgrees Ω x E)
    (h' : RayAgrees Ω' x E') (ht : t < E) (ht' : t < E') : Ω.stream t = Ω'.stream t :=
  Option.some.inj ((h.getElem? ht).symm.trans (h'.getElem? ht'))
end RayAgrees
end DeciSigma1.Holes.Tail
