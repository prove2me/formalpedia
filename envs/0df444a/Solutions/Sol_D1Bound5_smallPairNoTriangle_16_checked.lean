-- Prove2me | solution 1 for D1Bound5.smallPairNoTriangle_16_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:59:59.708972+00:00
-- url     : https://prove2.me/submissions/fcbc7b04-a5db-4504-8a8a-8d3ac3ebf4fe

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
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs16_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared16_all_trace_zero_checked
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_zero
import Theorems.Thm_D1Bound5_smallPairSieve_0_2_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_0_2 smallPairLarge_16 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_zero (by decide)
    smallPairSieve_0_2 smallPairSieve_0_2_valid smallPairLarge_16
    PairGraphPrepared16.all_trace_zero_checked

end D1Bound5
end
