-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:06.796706+00:00
-- url     : https://prove2.me/submissions/a0a90d33-c261-4518-9592-ca5b90e7b9d9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_eq_sum_of

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
theorem _root_.solution (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : F.support ⊆ s ∨ G.support ⊆ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  apply fock_eq_sum_of
  intro α hF hG
  rcases h with h | h
  · exact h (mem_support_iff.mpr hF)
  · exact h (mem_support_iff.mpr hG)
end Formalism.MainNotions.PlaneGram
