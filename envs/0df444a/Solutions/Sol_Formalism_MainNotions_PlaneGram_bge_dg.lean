-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bge_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:40.42584+00:00
-- url     : https://prove2.me/submissions/bad56427-ec9d-4d54-ab59-66f58be19ab1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


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
theorem _root_.solution {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K} (hf : ∀ α, vge v a (f α))
    (hF : bge v b F) : bge v (a + b) (dg f F) := fun α => by
  rw [coeff_dg]
  exact vge_mono' v (by linarith) (vge_mul' v (hf α) (hF α))
end Formalism.MainNotions.PlaneGram
