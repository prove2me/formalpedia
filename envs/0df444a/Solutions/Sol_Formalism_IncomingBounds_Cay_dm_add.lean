-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dm_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:04.683959+00:00
-- url     : https://prove2.me/submissions/1ef1f73d-defd-429c-92b7-927838e5645d

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_add

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
theorem _root_.solution {σ : Type} (m : σ →₀ ℕ) (Q Q' : MvPolynomial σ K) :
    dm m (Q + Q') = dm m Q + dm m Q' := by
  unfold dm
  exact supp_sum_add (fun a x => if m ≤ a then
      monomial (a - m) (x * ((Formalism.IncomingBounds.mfact a : K) / (Formalism.IncomingBounds.mfact (a - m) : K))) else 0)
    (fun a => by simp) (fun a x y => by by_cases h : m ≤ a <;> simp [h, add_mul]) Q Q'
end Formalism.IncomingBounds.Cay
