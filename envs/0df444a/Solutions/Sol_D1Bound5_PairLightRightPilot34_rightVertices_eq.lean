-- Prove2me | solution 1 for D1Bound5.PairLightRightPilot34.rightVertices_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:03.265318+00:00
-- url     : https://prove2.me/submissions/2735f6d2-6d36-4edc-af2e-38ba0902e9ec

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightRightData34_Definitions_001

section
namespace D1Bound5.PairLightRightPilot34
set_option maxRecDepth 100000
set_option maxHeartbeats 0



/-- The independent literal coordinate list is the exact original right class,
including its ordering and full coverage. This linear check is separate from
the expensive all-pairs computation in the arithmetic-only module. -/
theorem _root_.solution :
    rightVertices =
      (pairSplitByMask smallPairLarge_34 PairGraphPrepared34.colors).2.map
        pairLightCoordinates := by
  decide +kernel







end D1Bound5.PairLightRightPilot34
end
