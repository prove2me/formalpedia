-- Prove2me | solution 1 for DensInertW.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:02.725851+00:00
-- url     : https://prove2.me/submissions/ce2482b0-cea2-492d-b4f1-b16089e80d57

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
theorem _root_.solution (h2 : Module.finrank K L = 2) (x : L) : conj K (conj K x) = x :=
  frob_frob h2 x
end DensInertW
