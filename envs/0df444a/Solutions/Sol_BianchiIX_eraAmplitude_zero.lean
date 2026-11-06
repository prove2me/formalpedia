-- Prove2me | solution 1 for BianchiIX.eraAmplitude_zero
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:03:15.868245+00:00
-- url     : https://prove2.me/submissions/4372290a-6f5c-4f96-ad85-89f3b2582129

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


@[simp] theorem solution (B : ℝ) : eraAmplitude B 0 = B := by
  simp [eraAmplitude]
