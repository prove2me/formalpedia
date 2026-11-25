-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_five_lemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:47.767642+00:00
-- url     : https://prove2.me/submissions/4b4dfd78-45ad-4476-9e41-b4e3b84644c9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PlaneGramTheoremOfLemmas
import Theorems.Thm_Formalism_MainNotions_PlaneGram_plane_gram_theorem_of_combined_lemmas
import Theorems.Thm_Formalism_MainNotions_PlaneGram_segStep_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepBC_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepB_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepC_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepDEF_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepE_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepG_of
import Theorems.Thm_Formalism_MainNotions_PlaneGram_stepP_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (h1 : 1 ≤ C0) (hV2 : V2 K) (hSPAN : SPAN K v p) (hPROJ : PROJ K v p C0)
    (hDIG : DIG K v p) (hDER : DER K v p) : LiftBoundUniform K v p C0 :=
  plane_gram_theorem_of_combined_lemmas h1 (stepBC_of (stepB_of h1 hV2 hPROJ) (stepC_of hV2 (segStep_of hSPAN)))
    (stepDEF_of h1 hDIG (stepG_of hV2) (stepP_of v p C0 h1 hPROJ) (stepE_of v p hV2 hDER))
end Formalism.MainNotions.PlaneGram
