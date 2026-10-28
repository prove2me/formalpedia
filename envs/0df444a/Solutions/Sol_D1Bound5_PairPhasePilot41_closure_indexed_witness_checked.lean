-- Prove2me | solution 1 for D1Bound5.PairPhasePilot41.closure_indexed_witness_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:09.653276+00:00
-- url     : https://prove2.me/submissions/21c8ad99-e0bd-45cd-9e94-093cf22bd6f0

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
import Definitions.Def_D1Bound5_SmallPairIndexedClosure41_Definitions
import Definitions.Def_D1Bound5_SmallPairPhaseData41_Definitions
import Definitions.Def_D1Bound5_SmallPairWitnessData41_Definitions

section
namespace D1Bound5.PairPhasePilot41
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairClosureIndexedWitnessBool anchorA anchorB anchorRootWitness (10^1100)
      closure closureWitnesses indexedClosureDestinations = true := by
  decide +kernel



end D1Bound5.PairPhasePilot41
end
