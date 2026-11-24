-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:02.520809+00:00
-- url     : https://prove2.me/submissions/ddb871e1-c867-45ae-803b-68a15624487f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_comm
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_smul_left

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
theorem _root_.solution (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c * fock F G := by
  rw [fock_comm, fock_smul_left, fock_comm]
end Formalism.MainNotions.PlaneGram
