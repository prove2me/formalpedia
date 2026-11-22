-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.le_rpow_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:45.580955+00:00
-- url     : https://prove2.me/submissions/7b951ece-f16c-4d5d-babf-062ec465a442

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
theorem _root_.solution {Y C : ℝ} (hY : 2 ≤ Y) (hC : 0 ≤ C) : C ≤ Y ^ (2 * C) := by
  have hY0 : 0 < Y := by linarith
  rw [Real.rpow_def_of_pos hY0]
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have := Real.add_one_le_exp (Real.log Y * (2 * C))
  nlinarith
end Formalism.HermitianLatticeCounting.P
