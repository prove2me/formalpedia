-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_lemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:38.872159+00:00
-- url     : https://prove2.me/submissions/36ffe2e3-22a5-4569-9b05-cb77b129a5e8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PlaneGramTheoremOfLemmas
import Theorems.Thm_Formalism_MainNotions_PlaneGram_plane_gram_theorem_of_five_lemmas

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
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
    (C0 : ℝ), LiftBoundOfHypotheses K v p C0 :=
  fun _ _ _ _ _ _ h1 hV2 hS hP hDIG hDER => plane_gram_theorem_of_five_lemmas h1 hV2 hS hP hDIG hDER
end Formalism.MainNotions.PlaneGram
