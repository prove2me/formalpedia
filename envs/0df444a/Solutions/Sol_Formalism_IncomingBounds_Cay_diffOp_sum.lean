-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:22.47991+00:00
-- url     : https://prove2.me/submissions/9ede3f48-09ce-4d04-9a7b-8cac2f61485e

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_add
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_zero

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
theorem _root_.solution {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (Q : MvPolynomial σ K) :
    diffOp (∑ b ∈ s, f b) Q = ∑ b ∈ s, diffOp (f b) Q := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, diffOp_zero]) ?_
  intro b s hb ih
  rw [Finset.sum_insert hb, Finset.sum_insert hb, diffOp_add, ih]
end Formalism.IncomingBounds.Cay
