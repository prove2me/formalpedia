-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:45.966267+00:00
-- url     : https://prove2.me/submissions/26179f90-e977-4443-a71f-17cc5def99d4

import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (c : ℂ) (a : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (c • a) w = c * evalL1PowerSeries a w := by
  change l1EvalOperator w (c • a) = _
  rw [map_smul]
  rfl
end ClassicalComplexWPT
