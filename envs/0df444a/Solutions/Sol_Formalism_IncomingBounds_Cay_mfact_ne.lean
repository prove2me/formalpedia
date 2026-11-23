-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.mfact_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.127366+00:00
-- url     : https://prove2.me/submissions/2b87881e-623a-4943-ab26-5e50ec2b7fd3

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
theorem _root_.solution {σ : Type} (b : σ →₀ ℕ) : (mfact b : K) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold Formalism.IncomingBounds.mfact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _
end Formalism.IncomingBounds.Cay
