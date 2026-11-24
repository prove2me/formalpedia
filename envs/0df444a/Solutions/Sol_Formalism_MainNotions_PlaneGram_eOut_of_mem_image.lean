-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eOut_of_mem_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:40.206272+00:00
-- url     : https://prove2.me/submissions/d677a1ce-6da1-4606-9def-c88f23b0f7f2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eOut


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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out]
    (F : MvPolynomial (L × Fin r) K) {μ : L × Fin r →₀ ℕ} (hμ : μ ∈ F.support.image (eOut out)) :
    eOut out μ = μ := by
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  exact eOut_eOut out α
end Formalism.MainNotions.PlaneGram
