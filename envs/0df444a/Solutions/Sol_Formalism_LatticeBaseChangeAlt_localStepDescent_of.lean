-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localStepDescent_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:52:31.3058+00:00
-- url     : https://prove2.me/submissions/f8cfff3d-c279-4f20-8b05-cd5bd11d4956

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeDescentAlt_span_inf_eq
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeDescentAlt_fg_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution (h2 : FinrankSpanImage) (h3 : SpanImageInf) (h4 : RelIndexSpanImage) :
    LocalStepDescent := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ' M Θ V'
    hM hΘ d Y Z e h
  rw [h3 O O' K K' V V₁ j hj M V' hM, h3 O O' K K' V V₁ j hj Θ V' hΘ,
    h2 O O' K K' V V₁ j hj V',
    h4 O O' K K' V V₁ j hj ϖ hϖ hϖ' _ _ (LatticeDescentAlt.fg_inf M hM _) (LatticeDescentAlt.fg_inf Θ hΘ _)
      (by rw [LatticeDescentAlt.span_inf_eq M hM V', LatticeDescentAlt.span_inf_eq Θ hΘ V'])] at h
  exact h
end Formalism.LatticeBaseChangeAlt
