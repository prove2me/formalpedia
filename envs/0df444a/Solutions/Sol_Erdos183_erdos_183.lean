-- Prove2me | solution 1 for Erdos183.erdos_183
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:36:18.191778+00:00
-- url     : https://prove2.me/submissions/fcc7cff1-66e8-4656-a20a-4d0f3c8f711e

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Erdos183_divergentRamseyRoot

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  exact divergentRamseyRoot
