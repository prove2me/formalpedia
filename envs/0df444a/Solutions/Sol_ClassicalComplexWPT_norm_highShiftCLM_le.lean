-- Prove2me | solution 1 for ClassicalComplexWPT.norm_highShiftCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:07.837481+00:00
-- url     : https://prove2.me/submissions/d505e0d1-71b5-4be6-abf0-da107bed0bb1

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
theorem _root_.solution (d : ℕ) : ‖highShiftCLM (A := A) d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖highShift d f‖ ≤ 1 * ‖f‖
  simpa using norm_highShift_le (A := A) d f
end ClassicalComplexWPT
