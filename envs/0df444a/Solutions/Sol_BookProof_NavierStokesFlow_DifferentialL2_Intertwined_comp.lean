-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.Intertwined.comp
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T08:56:42.26659+00:00
-- url     : https://prove2.me/submissions/a0212b6a-f08b-49ef-a1b7-ca33f5a8d0c9

import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.NavierStokesFlow.DifferentialL2

-- Direct proof from the registered intertwining equation and linearity.
theorem solution {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T.comp S) (T'.comp S') := by
  intro x
  change T' (S' (embedCore x)) = embedCore (T (S x))
  rw [hS x, hT (S x)]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
