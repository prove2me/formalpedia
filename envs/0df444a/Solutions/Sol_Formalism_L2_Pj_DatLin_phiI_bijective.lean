-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.phiI_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:25.793981+00:00
-- url     : https://prove2.me/submissions/c880bf99-fd54-44ed-8f39-79349be37e14

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Formalism_L2_Pj_DatLin_phi1_bijective
import Theorems.Thm_Formalism_L2_Pj_DatLin_phiI_eq

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
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
variable {Ψ}
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phiI (ι := ι) Ψ) := by
  constructor
  · intro t t' h
    apply (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).injective
    funext i
    apply (phi1_bijective hΨ).1
    funext τ
    rw [← phiI_eq, ← phiI_eq, h]
  · intro u
    choose y hy using fun i => (phi1_bijective hΨ).2 (fun τ => u τ i)
    refine ⟨(TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).symm y, ?_⟩
    funext τ i
    rw [phiI_eq, LinearEquiv.apply_symm_apply, hy]
end Formalism.L2.Pj.DatLin
