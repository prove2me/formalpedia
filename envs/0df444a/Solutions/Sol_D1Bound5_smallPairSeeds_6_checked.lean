-- Prove2me | solution 1 for D1Bound5.smallPairSeeds_6_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:51.966426+00:00
-- url     : https://prove2.me/submissions/186b3e15-09fb-4100-9db5-03d49dd48105

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairSeedsCoveredBool smallPairA_6 smallPairB_6
      seedRootDisk_0_1 smallPairClosure_6 = true := by
  decide +kernel





end D1Bound5
end
