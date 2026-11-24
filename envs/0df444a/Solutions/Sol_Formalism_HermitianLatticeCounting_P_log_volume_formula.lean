-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.log_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:36.043795+00:00
-- url     : https://prove2.me/submissions/d0184d8e-9962-48be-85a0-9f1e79505801

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
theorem _root_.solution : LogVolume := by
  intro f j ts h0 h1
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 (by norm_num)]
  congr 2
  field_simp
end Formalism.HermitianLatticeCounting.P
