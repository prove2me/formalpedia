-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:31:47.607804+00:00
-- url     : https://prove2.me/submissions/2e900390-335a-4cd5-bc20-cc378c2b5df9

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
theorem _root_.solution (F F' G : MvPolynomial σ K) : fock (F + F') G = fock F G + fock F' G := by
  rw [fock_eq_sum (F + F') G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F' G G.support (Or.inr (Finset.Subset.refl _)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_add]; ring
end Formalism.MainNotions.PlaneGram
