-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:15.304563+00:00
-- url     : https://prove2.me/submissions/c681213f-14aa-498a-96f2-f17863d8890f

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_add
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_eq

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
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {σ : Type} (P P' Q : MvPolynomial σ K) :
    diffOp (P + P') Q = diffOp P Q + diffOp P' Q := by
  rw [diffOp_eq, diffOp_eq, diffOp_eq]
  exact supp_sum_add (fun m x => x • dm m Q) (fun _ => zero_smul _ _)
    (fun _ x y => add_smul x y _) P P'
end Formalism.IncomingBounds.Cay
