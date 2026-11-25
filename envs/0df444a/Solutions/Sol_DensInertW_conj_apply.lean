-- Prove2me | solution 1 for DensInertW.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:47.594828+00:00
-- url     : https://prove2.me/submissions/bbdc7757-2cec-4930-866e-9e2283f31ee0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero

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
omit [Fintype L]
namespace DensInertW
theorem _root_.solution (x : L) : conj K x = x ^ Fintype.card K := rfl
end DensInertW
