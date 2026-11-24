-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:30.136801+00:00
-- url     : https://prove2.me/submissions/a5ed07c4-7448-4df5-8612-23317019f50f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_comm
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_neg_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F G : MvPolynomial σ K) : fock F (-G) = -fock F G := by
  rw [fock_comm, fock_neg_left, fock_comm]
end Formalism.MainNotions.PlaneGram
