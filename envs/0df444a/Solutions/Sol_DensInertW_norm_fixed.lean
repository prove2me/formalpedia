-- Prove2me | solution 1 for DensInertW.norm_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:14.426895+00:00
-- url     : https://prove2.me/submissions/3f3941b4-03f2-40df-9750-887bbbaeeae7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Theorems.Thm_DensInertW_frob_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace DensInertW
theorem _root_.solution (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ (Fintype.card K + 1)) ^ Fintype.card K = x ^ (Fintype.card K + 1) := by
  rw [← pow_mul, mul_comm, pow_mul, pow_succ, frob_frob h2, ← pow_succ']
end DensInertW
