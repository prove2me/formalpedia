-- Prove2me | solution 1 for Formalism.L2.LamCM.substFr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:13.080061+00:00
-- url     : https://prove2.me/submissions/c9845485-cc3c-4cd7-bcf4-eb8208fed692

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Theorems.Thm_P2M_Formalism_L2_LamCM_bind__eq_self_of_27fe4921ee16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
variable {B : Type} {m : B → ℕ}
namespace Formalism.L2.LamCM
theorem _root_.solution {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) :
    substFr (fun b => (1 : Matrix (Fin (m b)) (Fin (m b)) R)) P = P := by
  unfold substFr
  apply bind₁_eq_self_of
  rintro ⟨b, i, k⟩
  simp [Matrix.one_apply]
end Formalism.L2.LamCM
