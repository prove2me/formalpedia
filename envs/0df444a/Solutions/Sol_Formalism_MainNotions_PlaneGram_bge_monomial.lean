-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bge_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:41.846825+00:00
-- url     : https://prove2.me/submissions/1d3d7df4-d2a0-41dd-b3f9-ce00b6342cc8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b

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
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a : ℝ} (α : σ →₀ ℕ) {c : K} (hc : vge v a c) :
    bge v (a + vN v (fact α) / 2) (monomial α c) := fun β => by
  classical
  rw [coeff_monomial]
  split_ifs with h
  · rw [← h]; exact vge_mono' v (by linarith) hc
  · exact vge_zero' v _
end Formalism.MainNotions.PlaneGram
