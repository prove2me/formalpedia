-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:01.225917+00:00
-- url     : https://prove2.me/submissions/5fefa36f-e758-45ea-9177-777668257f2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inl
import Theorems.Thm_P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {κ₁ κ₂ : Type*} (v : κ₁ → MvPolynomial S₁ K) (w : κ₂ → MvPolynomial S₂ K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K fun p : κ₁ × κ₂ => rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
  have h := (hw.tmul_of_isDomain hv).comp Prod.swap Prod.swap_injective
  let e : TensorProduct K (MvPolynomial S₂ K) (MvPolynomial S₁ K) ≃ₗ[K] MvPolynomial (S₁ ⊕ S₂) K :=
    ((algebraTensorAlgEquiv K (MvPolynomial S₂ K) (σ := S₁)).restrictScalars K).toLinearEquiv.trans
      (sumAlgEquiv K S₁ S₂).symm.toLinearEquiv
  have he : ∀ p : κ₁ × κ₂, e (TensorProduct.tmul K (w p.2) (v p.1)) =
      rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
    intro p
    apply (sumAlgEquiv K S₁ S₂).injective
    simp [e, algebraTensorAlgEquiv_tmul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C', smul_eq_C_mul, MvPolynomial.algebraMap_eq,
      mul_comm]
  have h2 := h.map' e.toLinearMap e.ker
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, LinearEquiv.coe_coe, he] using h2
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
