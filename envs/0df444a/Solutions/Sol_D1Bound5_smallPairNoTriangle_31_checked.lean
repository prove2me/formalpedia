-- Prove2me | solution 1 for D1Bound5.smallPairNoTriangle_31_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:59:57.949496+00:00
-- url     : https://prove2.me/submissions/e4325f84-1eb0-4448-b514-ef340ccc4ea9

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared31_all_trace_zero_checked
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_zero
import Theorems.Thm_D1Bound5_smallPairSieve_0_5_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_0_5 smallPairLarge_31 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_zero (by decide)
    smallPairSieve_0_5 smallPairSieve_0_5_valid smallPairLarge_31
    PairGraphPrepared31.all_trace_zero_checked

end D1Bound5
end
