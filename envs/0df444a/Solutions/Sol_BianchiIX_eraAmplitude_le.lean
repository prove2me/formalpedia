-- Prove2me | solution 1 for BianchiIX.eraAmplitude_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:03:19.519194+00:00
-- url     : https://prove2.me/submissions/80ec70ae-9b19-42a1-b6c2-3d8e88497578

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


theorem solution {B : ℝ} (hB : 0 ≤ B) (hB1 : B ≤ 1) (m : ℕ) : eraAmplitude B m ≤ B :=
  Real.rpow_le_self_of_le_one hB hB1 (one_le_pow₀ (by norm_num))
