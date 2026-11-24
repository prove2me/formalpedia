-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_eq_out_mul_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:17.148231+00:00
-- url     : https://prove2.me/submissions/2eb12199-cf5d-499a-8c04-4d45e6a781ba

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_of_disjoint
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn_n
import Theorems.Thm_Formalism_MainNotions_PlaneGram_disjoint_eOut_eIn

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
theorem _root_.solution {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α : L × Fin r →₀ ℕ) : fact α = fact (eOut out α) * fact (eIn out α) := by
  conv_lhs => rw [← eOut_add_eIn_n out α]
  exact fact_add_of_disjoint (disjoint_eOut_eIn out α α)
end Formalism.MainNotions.PlaneGram
