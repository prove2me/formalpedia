-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.two_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:11.433909+00:00
-- url     : https://prove2.me/submissions/baab7b6b-c511-49e5-ac2a-99e717f3b1d5

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Formalism_L2_Pj_DatLin_conj_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have h1 : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ComplexEmbedding.conjugate σ, (conj_mem_iff hΨ σ).2 h, by simp [ComplexEmbedding.conjugate]⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΨ τ).1 hτ
  have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := by
    intro a c h
    simpa [ComplexEmbedding.conjugate] using congrArg star h
  have h2 : (Ψ.image ComplexEmbedding.conjugate).card = Ψ.card := Finset.card_image_of_injective _ hinj
  have h3 := Finset.card_compl Ψ
  have h4 := Embeddings.card E ℂ
  have h5 := Finset.card_le_univ Ψ
  rw [h1, h2] at h3
  omega
end Formalism.L2.Pj.DatLin
