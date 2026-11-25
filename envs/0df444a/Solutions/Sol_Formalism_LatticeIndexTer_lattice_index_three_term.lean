-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_index_three_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:57.282031+00:00
-- url     : https://prove2.me/submissions/405704e8-54ad-4a65-9d12-5446b08a7f1b

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_arith3
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idxDet_core
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_det_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
namespace Formalism.LatticeIndexTer
theorem _root_.solution : ThreeIdx := by
  intro O K X₁ X₂ X₃ X₄ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    b₁ b₂ b₃ b₄ θ' j θ a b ha hb h
  dsimp only
  obtain ⟨a1, c1, ha1, hc1, h1⟩ := LatticeIndexDeterminant.det_frac (O := O) b₁ b₂ θ'
  obtain ⟨a2, c2, ha2, hc2, h2⟩ := LatticeIndexDeterminant.det_frac (O := O) b₂ b₃ j
  obtain ⟨a3, c3, ha3, hc3, h3⟩ := LatticeIndexDeterminant.det_frac (O := O) b₃ b₄ θ
  rw [LatticeIndexDeterminant.idxDet_core b₁ b₂ θ' a1 c1 ha1 hc1 h1, LatticeIndexDeterminant.idxDet_core b₂ b₃ j a2 c2 ha2 hc2 h2,
    LatticeIndexDeterminant.idxDet_core b₃ b₄ θ a3 c3 ha3 hc3 h3]
  have hcomp : LinearMap.toMatrix b₁ b₄
      ((θ : X₃ →ₗ[K] X₄) ∘ₗ (j : X₂ →ₗ[K] X₃) ∘ₗ (θ' : X₁ →ₗ[K] X₂)) =
      LinearMap.toMatrix b₃ b₄ (θ : X₃ →ₗ[K] X₄) *
        (LinearMap.toMatrix b₂ b₃ (j : X₂ →ₗ[K] X₃) * LinearMap.toMatrix b₁ b₂ (θ' : X₁ →ₗ[K] X₂)) := by
    rw [LinearMap.toMatrix_comp b₁ b₃ b₄, LinearMap.toMatrix_comp b₁ b₂ b₃]
  rw [hcomp, Matrix.det_mul, Matrix.det_mul] at h
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hrel : a * (c1 * c2 * c3) = b * (a1 * a2 * a3) := by
    apply hinj
    simp only [map_mul]
    rw [h, h1, h2, h3]
    ring
  have hv := congrArg (IsDiscreteValuationRing.addVal O) hrel
  simp only [IsDiscreteValuationRing.addVal_mul] at hv
  have hne : ∀ x : O, x ≠ 0 → IsDiscreteValuationRing.addVal O x ≠ ⊤ :=
    fun x hx h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  exact LatticeIndexDeterminant.arith3 _ _ _ _ _ _ _ _ hv (hne _ ha) (hne _ hb) (hne _ ha1) (hne _ hc1)
    (hne _ ha2) (hne _ hc2) (hne _ ha3) (hne _ hc3)
end Formalism.LatticeIndexTer
