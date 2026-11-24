-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.conj_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:55.186804+00:00
-- url     : https://prove2.me/submissions/005d0278-9a4c-4899-a0e4-d6fed52e13f2

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta

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
theorem _root_.solution (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ∈ Ψ ↔ σ ∉ Ψ := by
  rw [hΨ]
  simp [ComplexEmbedding.conjugate]
end Formalism.L2.Pj.DatLin
