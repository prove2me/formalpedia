-- Prove2me | solution 1 for D1Bound5.smallPairs_0_3_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:43.239994+00:00
-- url     : https://prove2.me/submissions/fc7a9730-b89a-4f74-af2b-30894ea7af3d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000























































































theorem _root_.solution :
    smallPairClassifiedBool smallDisk_0_3 (smallPairTable 0 3) = true := by
  decide +kernel

























































end D1Bound5
end
