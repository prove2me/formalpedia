-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.repeatFactorRay_agrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:17.890839+00:00
-- url     : https://prove2.me/submissions/01d0e2b1-73a3-462a-8018-3dba4191564c

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_pumpFactor
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_streamPrefix_repeatFactorRay


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {x : List α} {c c' : ℕ} (hcc : c < c') (hc' : c' ≤ x.length) :
    RayAgrees (repeatFactorRay x c c' hcc hc') x c' := by
  refine ⟨hc', ?_⟩
  have h1 := streamPrefix_repeatFactorRay hcc hc' (c' - c)
  rw [show c + (c' - c) = c' by omega] at h1
  rw [h1]
  have h2 := pumpFactor_take (L := c' - c) hcc hc' le_rfl (p := c') le_rfl
  rwa [List.take_of_length_le (by rw [length_pumpFactor hcc hc']; omega)] at h2
end DeciSigma1.Holes.Tail
