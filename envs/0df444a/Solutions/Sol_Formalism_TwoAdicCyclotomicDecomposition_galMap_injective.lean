-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.galMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:10.467012+00:00
-- url     : https://prove2.me/submissions/cee10a21-219d-47dd-9d96-63e2cf355ae6

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_pm_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ne_zero_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_sgn_spec
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_ext

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
theorem _root_.solution (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) :
    Function.Injective (galMap h.1 a b) := by
  intro σ τ hστ
  simp only [galMap, Prod.mk.injEq] at hστ
  obtain ⟨h1, h2, h3⟩ := hστ
  apply layer_ext h
  · rw [← h.1.autToPow_spec ℚ σ, ← h.1.autToPow_spec ℚ τ, h1]
  · rw [sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 σ),
      sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 τ), h2]
  · rw [sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 σ),
      sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 τ), h3]
end Formalism.TwoAdicCyclotomicDecomposition
