-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_monomial_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:24.800045+00:00
-- url     : https://prove2.me/submissions/f947289e-23ce-46fd-928a-5337a842ed33

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
theorem _root_.solution (F : MvPolynomial σ K) (α : σ →₀ ℕ) (c : K) :
    fock F (monomial α c) = F.coeff α * c * (fact α : K) := by
  classical
  rw [fock_eq_sum F (monomial α c) {α} (Or.inr (support_monomial_subset)), Finset.sum_singleton,
    coeff_monomial, if_pos rfl]
end Formalism.MainNotions.PlaneGram
