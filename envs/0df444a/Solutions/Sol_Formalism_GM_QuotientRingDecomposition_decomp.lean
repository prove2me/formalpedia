-- Prove2me | solution 1 for Formalism.GM.QuotientRingDecomposition.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:53:03.310013+00:00
-- url     : https://prove2.me/submissions/3cf0a93b-dcd5-42db-b124-d694f774f020

import Definitions.Def_Formalism_MahlerMeasure_Statement
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TrueRing
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial
open Formalism.GM.QuotientRingDecomposition
variable {R : Type} [CommRing R] {r Q : ℕ}
namespace Formalism.GM.QuotientRingDecomposition
theorem _root_.solution (hQ : 0 < Q) (m : Fin r →₀ ℕ) : E (modQ hQ m) + Q • divQ Q m = m := by
  ext i
  simp [modQ, Nat.mod_add_div]
end Formalism.GM.QuotientRingDecomposition
