-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:31.915565+00:00
-- url     : https://prove2.me/submissions/68409b6f-dbe2-48ba-8be1-82a896f28957

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_add_left
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
theorem _root_.solution (F F' G : MvPolynomial σ K) : fock (F - F') G = fock F G - fock F' G := by
  rw [sub_eq_add_neg, fock_add_left, fock_neg_left, ← sub_eq_add_neg]
end Formalism.MainNotions.PlaneGram
