-- Prove2me | solution 1 for Formalism.L2.LamCM.evalFr_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:35.598043+00:00
-- url     : https://prove2.me/submissions/a4e68af9-7de3-4d88-9283-b7d79fcc1840

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma

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
theorem _root_.solution {R : Type} [CommRing R] (a : R) (P : MvPolynomial (FrVar m) R)
    (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : evalFr (C a * P) Y = a * evalFr P Y := by
  unfold evalFr
  simp
end Formalism.L2.LamCM
