-- Prove2me | solution 1 for D1Bound5.smallPairTable_1_1_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:04.348299+00:00
-- url     : https://prove2.me/submissions/874ee947-7925-4a40-aed8-69f67a831db1

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
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000













































theorem _root_.solution :
    smallPairs_1_1.toFinset = smallPairRepresentatives_1_1.biUnion (smallTripleOrbit 1) := by
  decide +kernel



































































































end D1Bound5
end
