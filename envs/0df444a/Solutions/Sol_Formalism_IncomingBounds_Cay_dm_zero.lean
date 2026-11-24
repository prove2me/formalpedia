-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:05.353934+00:00
-- url     : https://prove2.me/submissions/2e4f607f-c39b-4d24-b3b6-a62fdd5e9465

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_mfact_ne

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
theorem _root_.solution {σ : Type} (Q : MvPolynomial σ K) : dm 0 Q = Q := by
  unfold dm
  conv_rhs => rw [MvPolynomial.as_sum Q]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [if_pos zero_le, tsub_zero, div_self (mfact_ne a), mul_one]
end Formalism.IncomingBounds.Cay
