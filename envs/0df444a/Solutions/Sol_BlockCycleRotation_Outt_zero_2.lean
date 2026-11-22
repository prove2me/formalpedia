-- Prove2me | solution 2 for BlockCycleRotation.Outt_zero
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:02:53.38896+00:00
-- url     : https://prove2.me/submissions/90f1e4b5-90dc-457f-a263-ef1cb7acfdc8

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem solution : Outt 0 = 0 := by
  simp [Outt]
