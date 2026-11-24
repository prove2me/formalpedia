-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.ddet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.631282+00:00
-- url     : https://prove2.me/submissions/eff7e669-6a31-42bd-8e26-804a870559fd

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_der_det
import Theorems.Thm_Formalism_IncomingBounds_Cay_dMg

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
theorem _root_.solution {n : ℕ} (i j : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n).det = adjugate (Mg K n) j i := by
  rw [der_det]
  simp only [dMg]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.IncomingBounds.Cay
