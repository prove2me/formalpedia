-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.mkRay_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:56.828395+00:00
-- url     : https://prove2.me/submissions/2f2adc17-26df-4137-a71f-92b0228df0b4

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {dflt : Ray α} {x : List α} {c c' : ℕ} (h : c < c' ∧ c' ≤ x.length) :
    mkRay dflt x c c' = repeatFactorRay x c c' h.1 h.2 := dif_pos h
end DeciSigma1.Holes.Tail
