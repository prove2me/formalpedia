-- Prove2me | solution 1 for Formalism.L2.LamCM.substFr_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:25.095676+00:00
-- url     : https://prove2.me/submissions/24906383-e0ab-4c25-8e0c-10988076e34b

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
theorem _root_.solution {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (a : R)
    (P : MvPolynomial (FrVar m) R) : substFr U (C a * P) = C a * substFr U P := by
  unfold substFr
  rw [map_mul, bind₁_C_right]
end Formalism.L2.LamCM
