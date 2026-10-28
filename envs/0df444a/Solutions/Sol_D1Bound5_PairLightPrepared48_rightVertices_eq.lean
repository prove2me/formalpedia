-- Prove2me | solution 1 for D1Bound5.PairLightPrepared48.rightVertices_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:31.178992+00:00
-- url     : https://prove2.me/submissions/3ce82b7b-935f-453d-9ebf-b90b8f4bda41

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_001

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.solution :
    rightVertices = (pairSplitByMask smallPairLarge_48 PairGraphPrepared48.colors).2.map pairLightCoordinates := by
  decide +kernel







end D1Bound5.PairLightPrepared48
end
