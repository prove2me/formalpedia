-- Prove2me | solution 1 for D1Bound5.smallPairNoTriangle_32_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:59:57.278681+00:00
-- url     : https://prove2.me/submissions/8fb25c06-b6d8-4884-b544-ad4fa4ee7c90

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_6_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared32_all_trace_zero_checked
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_zero
import Theorems.Thm_D1Bound5_smallPairSieve_0_6_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_0_6 smallPairLarge_32 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_zero (by decide)
    smallPairSieve_0_6 smallPairSieve_0_6_valid smallPairLarge_32
    PairGraphPrepared32.all_trace_zero_checked

end D1Bound5
end
