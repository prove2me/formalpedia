-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:19.031593+00:00
-- url     : https://prove2.me/submissions/d374685d-a2b0-4d30-974f-1c5613986623

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
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, tm (p := p) LL j i c d := rfl
end Formalism.CountingSumsFrames
