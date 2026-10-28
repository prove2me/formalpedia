-- Prove2me | solution 1 for D1Bound5.smallPairSeeds_39_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:13.897992+00:00
-- url     : https://prove2.me/submissions/36606735-be4e-4ce2-ae8e-a0e02a884db8

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
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairSeedsCoveredBool smallPairA_39 smallPairB_39
      seedRootDisk_1_2 smallPairClosure_39 = true := by
  decide +kernel





end D1Bound5
end
