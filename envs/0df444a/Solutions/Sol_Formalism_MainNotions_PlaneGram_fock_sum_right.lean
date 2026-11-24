-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:05.392557+00:00
-- url     : https://prove2.me/submissions/605ae67a-9cab-4396-b188-944e66a8a188

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_comm
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sum_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (f : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, f i) = ∑ i ∈ s, fock F (f i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm _ _
end Formalism.MainNotions.PlaneGram
