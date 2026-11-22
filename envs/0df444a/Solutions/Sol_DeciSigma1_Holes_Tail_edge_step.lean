-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.edge_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:48.188143+00:00
-- url     : https://prove2.me/submissions/f97fc945-6e96-4d72-adb6-0230baa09a37

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_Ray_suffix_eq_cases
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_suffix_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {Ωh Ωx : Ray α} {a b Jx : ℕ} (heq : ∀ t, Ωh.stream (a + t) = Ωx.stream (b + t))
    (hb : b ≤ Jx) (hx : Jx < Ωx.onset) :
    Ωx.suffixBeforeOnset Jx <:+ Ωh.prefixBeforeOnset ∧ ∀ t, Ωh.stream (Ωh.onset + t) =
        Ωx.stream (Ωx.onset + t) := by
  rcases Ray.suffix_eq_cases heq with ⟨_, h2⟩ | ⟨_, h2⟩
  · omega
  · constructor
    · rw [Ray.prefixBeforeOnset, Ray.suffixBeforeOnset, streamPrefix_suffix_iff]
      refine ⟨by omega, fun t ht => ?_⟩
      have := heq (Jx - b + t)
      rw [show a + (Jx - b + t) = Ωh.onset - (Ωx.onset - Jx) + t by omega,
        show b + (Jx - b + t) = Jx + t by omega] at this
      exact this.symm
    · intro t
      have := heq (Ωh.onset - a + t)
      rwa [show a + (Ωh.onset - a + t) = Ωh.onset + t by omega,
        show b + (Ωh.onset - a + t) = Ωx.onset + t by omega] at this
end DeciSigma1.Holes.Tail
