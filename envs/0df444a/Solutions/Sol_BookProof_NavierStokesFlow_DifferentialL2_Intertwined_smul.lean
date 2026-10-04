-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.Intertwined.smul
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T08:56:39.654337+00:00
-- url     : https://prove2.me/submissions/af3b7149-7b0b-4b39-b878-cae5f0305fbe

import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.NavierStokesFlow.DifferentialL2

-- Direct proof from the registered intertwining equation and linearity.
theorem solution {T T'} (c : ℂ) (hT : Intertwined T T') :
    Intertwined (c • T) (c • T') := by
  intro x
  change c • T' (embedCore x) = embedCore (c • T x)
  rw [hT x, map_smul]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
