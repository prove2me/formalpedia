-- Prove2me | solution 1 for CovecW.sig_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:04.622895+00:00
-- url     : https://prove2.me/submissions/b5cd2c54-b9e7-44bc-9d34-b6f3371accc4

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
theorem _root_.solution (k r : ℕ) (a : Fin r) : sig k r (esI k r a) = eI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega
end CovecW
