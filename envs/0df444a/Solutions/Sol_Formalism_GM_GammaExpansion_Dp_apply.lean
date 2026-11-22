-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.Dp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:01.843979+00:00
-- url     : https://prove2.me/submissions/372f0e28-543e-4968-b56f-d3f5046dc416

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (v : σ) (p : MvPolynomial σ R) : Dp v p = pderiv v p := rfl
end Formalism.GM.GammaExpansion
