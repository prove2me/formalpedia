-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.sgn_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:04.86192+00:00
-- url     : https://prove2.me/submissions/a5d2d29f-1988-4251-83e2-ade4fabaf19a

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {x : L} (hx0 : x ≠ 0) {σ : Gal(L/ℚ)} (h : σ x = x ∨ σ x = -x) :
    σ x = (((sgn σ x : ℤˣ) : ℤ) : L) * x := by
  rcases h with h | h
  · rw [sgn_of_eq h, h]; simp
  · rw [sgn_of_neg hx0 h, h]; simp
end Formalism.TwoAdicCyclotomicDecomposition
