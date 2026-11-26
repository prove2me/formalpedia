-- Prove2me | solution 1 for ClassicalComplexWPT.norm_lowCutCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:08.272626+00:00
-- url     : https://prove2.me/submissions/bd392cb8-a41d-47bb-ab71-475c78d3e295

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) : ‖lowCutCLM (A := A) d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖lowCut d f‖ ≤ 1 * ‖f‖
  simpa using norm_lowCut_le (A := A) d f
end ClassicalComplexWPT
