-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared29.indexed_chunk08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:11.134206+00:00
-- url     : https://prove2.me/submissions/521faf29-1864-4a47-a102-6400aaa0f7a7

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
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData29_Definitions_003

section
namespace D1Bound5.PairGraphPrepared29
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both mutation signs use the complete original destination vertex list. -/
theorem _root_.solution :
    pairIndexedWitnessesPrefixBool smallPairA_29 smallPairB_29 anchorRoot
      (10^1100) smallPairClosure_29 64
      (witnesses.drop 512) (destinations.drop 512) = true := by
  decide +kernel

end D1Bound5.PairGraphPrepared29
end
