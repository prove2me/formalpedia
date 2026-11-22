-- Prove2me | solution 1 for Formalism.GM.QuotientRingDecomposition.E_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:22.52764+00:00
-- url     : https://prove2.me/submissions/4544aa03-96a2-4404-b557-9b428359f629

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
theorem _root_.solution (e : Fin r → Fin Q) (i : Fin r) : E e i = (e i : ℕ) := rfl
end Formalism.GM.QuotientRingDecomposition
