-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.Intertwined.add
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T08:56:36.984543+00:00
-- url     : https://prove2.me/submissions/9b5e040f-91f1-46db-a247-fea53cd4e833

import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.NavierStokesFlow.DifferentialL2

-- Direct proof from the registered intertwining equation and linearity.
theorem solution {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T + S) (T' + S') := by
  intro x
  change T' (embedCore x) + S' (embedCore x) = embedCore (T x + S x)
  rw [hT x, hS x, map_add]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
