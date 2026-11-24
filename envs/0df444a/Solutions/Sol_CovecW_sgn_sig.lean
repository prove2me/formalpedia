-- Prove2me | solution 1 for CovecW.sgn_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:53.557737+00:00
-- url     : https://prove2.me/submissions/1bcdaa2e-813b-4747-95b4-b8b65eb7f24b

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_sig_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  unfold sgn
  rw [sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)
end CovecW
