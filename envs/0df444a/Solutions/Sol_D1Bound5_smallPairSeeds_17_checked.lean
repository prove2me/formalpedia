-- Prove2me | solution 1 for D1Bound5.smallPairSeeds_17_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:10.879935+00:00
-- url     : https://prove2.me/submissions/db744a21-bba2-4174-8758-6bf5e3e22dbe

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairSeedsCoveredBool smallPairA_17 smallPairB_17
      seedRootDisk_0_2 smallPairClosure_17 = true := by
  decide +kernel





end D1Bound5
end
