-- Prove2me | solution 1 for Formalism.GM.QuotientRingDecomposition.divQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:23.915943+00:00
-- url     : https://prove2.me/submissions/c642e386-b03b-45e8-88cb-fec5dab155a9

import Definitions.Def_Formalism_MahlerMeasure_Statement
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TrueRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial
open Formalism.GM.QuotientRingDecomposition
variable {R : Type} [CommRing R] {r Q : ℕ}
namespace Formalism.GM.QuotientRingDecomposition
theorem _root_.solution (m : Fin r →₀ ℕ) (i : Fin r) : divQ Q m i = m i / Q := rfl
end Formalism.GM.QuotientRingDecomposition
