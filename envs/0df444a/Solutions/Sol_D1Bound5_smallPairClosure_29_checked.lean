-- Prove2me | solution 1 for D1Bound5.smallPairClosure_29_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:22:49.455283+00:00
-- url     : https://prove2.me/submissions/c4d03f00-326e-4e4a-b4d5-5827f50a55aa

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData29_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared29_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared29



theorem _root_.solution :
    pairClosureBool smallPairA_29 smallPairB_29
      (10^1100) smallPairClosure_29 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_29 smallPairB_29 anchorRoot
    (10^1100) smallPairClosure_29 witnesses destinations PairGraphPrepared29.indexed_checked

end D1Bound5
end
