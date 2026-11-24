-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.farA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:45.273669+00:00
-- url     : https://prove2.me/submissions/da788890-92f8-40b3-b75f-4c873deba40e

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farW_nonneg

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
theorem _root_.solution (B h ε : ℝ) (i : ℕ) : 0 ≤ farA B h ε i :=
  mul_nonneg (Real.exp_pos _).le (farW_nonneg _ _ _)
end Formalism.HermitianLatticeCounting.P
