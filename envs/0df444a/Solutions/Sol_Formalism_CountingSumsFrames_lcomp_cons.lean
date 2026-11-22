-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:21.049213+00:00
-- url     : https://prove2.me/submissions/c8f1c2af-ff3d-44b3-ab3f-c0ed1ffcddfa

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : ι → V →ₗ[K] V) (i : ι) (l : List ι) : lcomp φ (i :: l) = φ i ∘ₗ lcomp φ l := rfl
end Formalism.CountingSumsFrames
