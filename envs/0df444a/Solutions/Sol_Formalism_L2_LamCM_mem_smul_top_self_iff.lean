-- Prove2me | solution 1 for Formalism.L2.LamCM.mem_smul_top_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:34.762472+00:00
-- url     : https://prove2.me/submissions/4ba7ff6a-d962-4450-b437-234f8c871702

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt

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
open Polynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {R : Type} [CommRing R] (J : Ideal R) (y : R) :
    y ∈ J • (⊤ : Submodule R R) ↔ y ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
end Formalism.L2.LamCM
