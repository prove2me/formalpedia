-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layer_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:27.977984+00:00
-- url     : https://prove2.me/submissions/f83cfa82-f24f-4219-b1aa-fdcb2fe16ced

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
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (h : IsLayer n q d ζ a b) {σ τ : Gal(L/ℚ)} (h1 : σ ζ = τ ζ) (h2 : σ a = τ a)
    (h3 : σ b = τ b) : σ = τ := by
  have htop : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, h.2.2.2, IntermediateField.top_toSubalgebra]
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top htop
  intro x hx
  rcases hx with rfl | rfl | rfl
  · simpa using h1
  · simpa using h2
  · simpa using h3
end Formalism.TwoAdicCyclotomicDecomposition
