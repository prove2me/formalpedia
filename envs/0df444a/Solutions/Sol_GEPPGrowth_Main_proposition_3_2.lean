-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:48:12.31201+00:00
-- url     : https://prove2.me/submissions/e8d27d3b-c0b5-440f-9a50-5785170f24af

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

open GEPPGrowth.Main in
theorem solution (d : ℕ) (i : Fin (d+1)) :
    deletion i *ᵥ basisVector i = 0 := by
  ext a
  simp [Matrix.mulVec, dotProduct, deletion, basisVector, Equiv.swap_apply_eq_iff,
    Fin.succ_ne_zero]
