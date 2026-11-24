-- Prove2me | solution 1 for CovecW.sgn_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:50.333308+00:00
-- url     : https://prove2.me/submissions/0a6fab1f-44a4-4747-9a49-63a28c6eb296

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
theorem _root_.solution (k r : ℕ) (a : Fin r) : sgn k r (esI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]
end CovecW
