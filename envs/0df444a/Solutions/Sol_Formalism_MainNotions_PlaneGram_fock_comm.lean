-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:31:37.47309+00:00
-- url     : https://prove2.me/submissions/24b6fd46-f570-455c-b931-d83551842db7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_eq_sum

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
theorem _root_.solution (F G : MvPolynomial σ K) : fock F G = fock G F := by
  rw [fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))]
  unfold fock
  exact Finset.sum_congr rfl fun α _ => by ring
end Formalism.MainNotions.PlaneGram
