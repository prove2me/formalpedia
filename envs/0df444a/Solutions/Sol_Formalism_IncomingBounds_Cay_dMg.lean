-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dMg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.736551+00:00
-- url     : https://prove2.me/submissions/a1d5635e-690a-4c64-98aa-fd9ce7bf7218

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
theorem _root_.solution {n : ℕ} (i j p q : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n p q) = if p = i ∧ q = j then 1 else 0 := by
  classical
  rw [show Mg K n p q = X (Sum.inl (p, q)) from rfl, pderiv_X, Pi.single_apply]
  by_cases h : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : (Sum.inl (p, q) : Formalism.IncomingBounds.PVar n) ≠ Sum.inl (i, j) := by
      intro e
      apply h
      simpa using e
    rw [if_neg h, if_neg h']
end Formalism.IncomingBounds.Cay
