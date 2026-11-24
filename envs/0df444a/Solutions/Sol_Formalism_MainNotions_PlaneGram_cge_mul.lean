-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:43.986947+00:00
-- url     : https://prove2.me/submissions/09b7a465-e472-4b1a-9b7e-2c579ab83089

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} {a b : ℝ} {F G : MvPolynomial σ K} (hF : cge v a F) (hG : cge v b G) :
    cge v (a + b) (F * G) := by
  classical
  intro α
  rw [MvPolynomial.coeff_mul]
  exact vge_sum v _ _ fun x _ => vge_mul v (hF _) (hG _)
end Formalism.MainNotions.PlaneGram
