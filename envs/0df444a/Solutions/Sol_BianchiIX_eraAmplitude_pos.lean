-- Prove2me | solution 1 for BianchiIX.eraAmplitude_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:03:17.531597+00:00
-- url     : https://prove2.me/submissions/5a0cecea-d2df-4805-ad48-4b9cbdba3d44

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


theorem solution {B : ℝ} (hB : 0 < B) (m : ℕ) : 0 < eraAmplitude B m :=
  Real.rpow_pos_of_pos hB _
