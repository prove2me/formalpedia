-- Prove2me | solution 1 for D1Bound5.smallPairNoTriangle_22_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:59:58.777623+00:00
-- url     : https://prove2.me/submissions/487cd7ce-e0c3-4e1e-96ef-e49942e86b60

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_003
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared22_all_trace_zero_checked
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_trace_zero_tau_one
import Theorems.Thm_D1Bound5_smallPairSieve_1_1_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    pairGraphTriangleFreeBool smallPairSieve_1_1 smallPairLarge_22 = true :=
  pairGraphTriangleFreeBool_of_trace_zero_tau_one (by decide)
    smallPairSieve_1_1 smallPairSieve_1_1_valid smallPairLarge_22
    PairGraphPrepared22.all_trace_zero_checked

end D1Bound5
end
