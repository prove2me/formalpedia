-- Prove2me | solution 1 for CovecW.sgn_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:52.725414+00:00
-- url     : https://prove2.me/submissions/4509d785-22d2-435e-beb6-f4bf8173f4b4

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft

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
theorem _root_.solution (k r : ℕ) (a : Fin r) : sgn k r (eI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]
end CovecW
