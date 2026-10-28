-- Prove2me | solution 1 for D1Bound5.smallPairNoTriangle_37_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:00:03.988265+00:00
-- url     : https://prove2.me/submissions/7001daaf-c090-42ec-bd99-5b73d0590dc4

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_003
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared37_all_trace_zero_checked
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_one
import Theorems.Thm_D1Bound5_smallPairSieve_1_2_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_1_2 smallPairLarge_37 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_one (by decide)
    smallPairSieve_1_2 smallPairSieve_1_2_valid smallPairLarge_37
    PairGraphPrepared37.all_trace_zero_checked

end D1Bound5
end
