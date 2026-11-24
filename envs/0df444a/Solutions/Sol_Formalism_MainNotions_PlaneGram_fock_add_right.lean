-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:05.272655+00:00
-- url     : https://prove2.me/submissions/68f55702-a236-4b40-8871-64fc440df982

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_comm
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_add_left

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
theorem _root_.solution (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  rw [fock_comm, fock_add_left, fock_comm G, fock_comm G']
end Formalism.MainNotions.PlaneGram
