-- Prove2me | solution 1 for CovecW.sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:06.082715+00:00
-- url     : https://prove2.me/submissions/9cbfa9c0-2c92-41dc-825f-1dd87c3c68b7

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [sig_val, sig_val]
  split_ifs <;> omega
end CovecW
