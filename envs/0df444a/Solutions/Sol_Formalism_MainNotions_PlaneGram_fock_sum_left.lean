-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:05.222311+00:00
-- url     : https://prove2.me/submissions/6e2ea8a6-c026-4ad1-ae94-943332c8b257

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_add_left
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_zero_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ i ∈ s, f i) G = ∑ i ∈ s, fock (f i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fock_add_left, ih]
end Formalism.MainNotions.PlaneGram
