-- Prove2me | solution 1 for BianchiIX.eraAmplitude_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:03:21.025503+00:00
-- url     : https://prove2.me/submissions/d6babf80-777d-4a5d-b1e7-4f2e807a8214

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


theorem solution {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    eraAmplitude B (m + 1) = eraAmplitude B m ^ (4 / 3 : ℝ) := by
  simp only [eraAmplitude, pow_succ, Real.rpow_mul hB]
