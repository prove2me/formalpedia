-- Prove2me | solution 1 for ClassicalComplexWPT.evalL1PowerSeries_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:21.520709+00:00
-- url     : https://prove2.me/submissions/3de34fc7-7300-4db1-8cb6-2f90eaad3b54

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (a b : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (a + b) w =
      evalL1PowerSeries a w + evalL1PowerSeries b w := by
  change l1EvalOperator w (a + b) = _
  exact map_add (l1EvalOperator w) a b
end ClassicalComplexWPT
