-- Prove2me | solution 1 for D1Bound5.smallPairPilotTraceZeroNoTriangle_41_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:00:00.572955+00:00
-- url     : https://prove2.me/submissions/e21c9424-1dfd-4aa5-84c3-4db98863ed9b

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
import Definitions.Def_D1Bound5_SmallPairBipartitePilotData41_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_one
import Theorems.Thm_D1Bound5_smallPairPilotAllTraceZero_41_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_2_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



/-- The original triangle predicate, obtained from the actual arithmetic
no-three theorem and the linear trace-coordinate certificate. -/
theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_1_2 smallPairPilotLarge_41 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_one (by decide)
    smallPairSieve_1_2 smallPairSieve_1_2_valid smallPairPilotLarge_41
    smallPairPilotAllTraceZero_41_checked

end D1Bound5
end
