-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.type_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:41.03695+00:00
-- url     : https://prove2.me/submissions/ccce7c5c-1f38-4a28-b1d1-da060cb262f8

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TypeCount := by
  intro q
  simp only [composition_card]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]; omega
end Formalism.HermitianLatticeCounting.P
