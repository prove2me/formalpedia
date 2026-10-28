-- Prove2me | solution 1 for D1Bound5.PairLightPrepared24.rightVertices_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:51.76002+00:00
-- url     : https://prove2.me/submissions/f25ee957-6744-43f2-83ab-cf0304da0034

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData24RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.solution :
    rightVertices = (pairSplitByMask smallPairLarge_24 PairGraphPrepared24.colors).2.map pairLightCoordinates := by
  decide +kernel







end D1Bound5.PairLightPrepared24
end
