-- Prove2me | solution 1 for Formalism.Q3.mq_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:37.346261+00:00
-- url     : https://prove2.me/submissions/001393b9-7837-42c4-9efb-a4d3bae5f304

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Theorems.Thm_Formalism_Q3_mq_sigma
import Theorems.Thm_Formalism_Q3_mq_algAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
namespace Formalism.Q3
theorem _root_.solution (h : IsMQ a α) : Function.Injective (galSign α) := by
  intro σ τ hst
  have hsub : ∀ x ∈ Set.range α, (σ : E →ₐ[ℚ] E) x = (τ : E →ₐ[ℚ] E) x := by
    rintro _ ⟨i, rfl⟩
    simp only [AlgEquiv.coe_algHom]
    rw [mq_sigma h σ i, mq_sigma h τ i, hst]
  have := AlgHom.ext_of_adjoin_eq_top (mq_algAdjoin h) hsub
  ext x
  exact DFunLike.congr_fun this x
end Formalism.Q3
