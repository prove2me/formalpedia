-- Prove2me | solution 1 for D1Bound5.PairPhasePilot41.closure_checked_by_indexed_witness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:29:23.914487+00:00
-- url     : https://prove2.me/submissions/5d94ed86-a1a0-47a1-acdd-66472b5cc7ee

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairIndexedClosure41_Definitions
import Definitions.Def_D1Bound5_SmallPairPhaseData41_Definitions
import Definitions.Def_D1Bound5_SmallPairWitnessData41_Definitions
import Theorems.Thm_D1Bound5_PairPhasePilot41_closure_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5.PairPhasePilot41
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairClosureBool anchorA anchorB (10^1100) closure = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) anchorA anchorB anchorRootWitness
    (10^1100) closure closureWitnesses indexedClosureDestinations closure_indexed_witness_checked

end D1Bound5.PairPhasePilot41
end
