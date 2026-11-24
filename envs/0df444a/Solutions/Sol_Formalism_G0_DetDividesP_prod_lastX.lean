-- Prove2me | solution 1 for Formalism.G0.DetDividesP.prod_lastX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:24.027798+00:00
-- url     : https://prove2.me/submissions/b00198d5-60fc-40be-9b66-74cd5474e8b0

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_lastIdx_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) {R : Type} [CommRing R] (u : R) :
    (∏ a : Fin r, if a.val + 1 = r then u else 1) = u := by
  have : (fun a : Fin r => if a.val + 1 = r then u else 1) =
      fun a => if (⟨r - 1, by omega⟩ : Fin r) = a then u else 1 := by
    funext a; simp only [lastIdx_iff hr, eq_comm]
  rw [this, Finset.prod_ite_eq]; simp
end Formalism.G0.DetDividesP
