-- Prove2me | solution 1 for BianchiIX.eraAmplitude_power_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:07:12.115992+00:00
-- url     : https://prove2.me/submissions/bf9f2829-3319-4b4a-bac5-caa58101b78d

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


theorem solution {B : ℝ} (hB : 0 < B) (p : ℝ) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p = eraAmplitude B m ^ p * eraAmplitude B m ^ (p / 3) := by
  rw [eraAmplitude_succ hB.le, ← Real.rpow_mul (eraAmplitude_pos hB m).le,
    ← Real.rpow_add (eraAmplitude_pos hB m)]
  congr 1
  ring
