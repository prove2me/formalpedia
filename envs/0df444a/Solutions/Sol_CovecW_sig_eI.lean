-- Prove2me | solution 1 for CovecW.sig_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:03.470693+00:00
-- url     : https://prove2.me/submissions/22ccd9a8-fae5-4e00-bf53-a08b39f80e93

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
theorem _root_.solution (k r : ℕ) (a : Fin r) : sig k r (eI k r a) = esI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega
end CovecW
