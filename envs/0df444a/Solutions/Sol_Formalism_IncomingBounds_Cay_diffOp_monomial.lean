-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:37.842953+00:00
-- url     : https://prove2.me/submissions/cdcb8e55-6277-43e2-9a57-cc8f8d578dbf

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_monomial
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
theorem _root_.solution {σ : Type} (m : σ →₀ ℕ) (c : K) (Q : MvPolynomial σ K) :
    diffOp (monomial m c) Q = c • dm m Q := by
  rw [diffOp_eq]
  exact supp_sum_monomial (fun m' x => x • dm m' Q) (fun _ => zero_smul _ _) m c
end Formalism.IncomingBounds.Cay
