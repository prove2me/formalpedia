-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared16.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:43.95089+00:00
-- url     : https://prove2.me/submissions/cae458ba-e7aa-4f76-bf70-e98a9aa18b88

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
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs16_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData16_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData16_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared16

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_16 smallPairB_16 anchorRoot
      (10^1100) smallPairClosure_16 witnesses destinations = true := by
  decide +kernel



end D1Bound5
end
