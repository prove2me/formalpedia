-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.RunCovers.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:39.596443+00:00
-- url     : https://prove2.me/submissions/dc88bec5-b305-4606-96fd-90b9696f6a8f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace RunCovers
theorem _root_.solution {rs runs : Finset (RunSpec k)} {i : Fin k} {p : ℕ} (h : RunCovers rs i p)
    (hsub : rs ⊆ runs) : RunCovers runs i p :=
  let ⟨r, hr, h1⟩ := h; ⟨r, hsub hr, h1⟩
end RunCovers
end DeciSigma1.Holes.Tail
