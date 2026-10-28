-- Prove2me | solution 1 for D1Bound5.smallPairClosure_17_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:06:02.361991+00:00
-- url     : https://prove2.me/submissions/019a105d-5465-40f2-8900-f3d2cd0260e9

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData17_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared17_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared17



theorem _root_.solution :
    pairClosureBool smallPairA_17 smallPairB_17
      (10^1100) smallPairClosure_17 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_17 smallPairB_17 anchorRoot
    (10^1100) smallPairClosure_17 witnesses destinations PairGraphPrepared17.indexed_checked

end D1Bound5
end
