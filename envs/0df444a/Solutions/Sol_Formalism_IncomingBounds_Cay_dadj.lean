-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dadj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:20.165851+00:00
-- url     : https://prove2.me/submissions/5689ddfb-a41a-4b64-acba-5d0c0f51ce67

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_der_adj
import Theorems.Thm_Formalism_IncomingBounds_Cay_dMg
import Theorems.Thm_Formalism_IncomingBounds_Cay_ddet

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
theorem _root_.solution {n : ℕ} (i j a b : Fin n) :
    (Mg K n).det * pderiv (Sum.inl (i, j)) (adjugate (Mg K n) a b) =
      adjugate (Mg K n) j i * adjugate (Mg K n) a b - adjugate (Mg K n) a i * adjugate (Mg K n) j b := by
  rw [der_adj, ddet]
  congr 1
  simp only [dMg]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro p' _ hp
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.IncomingBounds.Cay
