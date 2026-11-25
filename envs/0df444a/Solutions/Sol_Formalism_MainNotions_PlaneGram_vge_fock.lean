-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_fock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:16.758559+00:00
-- url     : https://prove2.me/submissions/d65a36c6-cf9e-4eb7-a122-912e6aa3306a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd

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
theorem _root_.solution {a b : ℝ} {F G : MvPolynomial σ K} (hF : bge v a F) (hG : bge v b G) :
    vge v (a + b) (fock F G) := by
  unfold fock
  apply vge_sum'
  intro α _
  have h1 := vge_mul' v (vge_mul' v (hF α) (hG α)) (vge_vN' v (fact α))
  exact vge_mono' v (by linarith) h1
end Formalism.MainNotions.PlaneGram
