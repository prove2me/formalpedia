-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:08.77051+00:00
-- url     : https://prove2.me/submissions/79454b83-2234-4bab-b90a-26125f35b396

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

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
theorem _root_.solution {σ : Type} (P Q : MvPolynomial σ K) :
    diffOp P Q = ∑ m ∈ P.support, coeff m P • dm m Q := by
  unfold Formalism.IncomingBounds.diffOp dm
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_assoc]
  · rw [smul_zero]
end Formalism.IncomingBounds.Cay
