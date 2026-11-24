-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP_opU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:53.953852+00:00
-- url     : https://prove2.me/submissions/2f26a87d-80c1-4df5-9efa-1d1f09b96590

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_comm_U_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (ψ : (Fin r → k) → R) (f : Fin r → k) :
    nmP (opU ψ) f = ∑ x ∈ univ.filter (fun x => pair f x = 1), nmV ψ x := by
  unfold nmP
  simp only [← comm_U_apply]
  unfold opU nmV
  exact Finset.sum_comm
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
