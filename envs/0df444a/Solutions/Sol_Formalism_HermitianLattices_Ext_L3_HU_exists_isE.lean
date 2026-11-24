-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_isE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:56:16.335827+00:00
-- url     : https://prove2.me/submissions/469b2aec-3350-41e6-bba9-064b3d48c8a3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCountPosBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_arch
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isUnif0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_det_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isLocUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP_iff_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_locF_iff_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_noncompactPart_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e, IsE h (locF 𝔭 (spanO b)) 𝔭 e := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  have hS := isLocUnif hK hF h𝔭 hu
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  obtain ⟨l, hl⟩ := exists_arch hS (fun p : κ × κ => (gramK h b)⁻¹ p.1 p.2)
  refine ⟨l, fun x hx t ht => ?_⟩
  rw [mem_locF_iff_repr]
  intro i
  have hv : ∀ j, (gramK h b *ᵥ b.equivFun x) j ∈ SP K 𝔭 := by
    intro j
    have h1 := hx (b j) (le_locF 𝔭 _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [← mem_SP_iff_locF, form_repr h b] at h1
    have hb1 : b.equivFun (b j) = Pi.single j 1 := by
      funext j'
      rw [Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    have hb2 : star (Pi.single j (1 : K) : κ → K) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rwa [hb1, hb2, single_one_dotProduct] at h1
  have hx' : b.equivFun x = (gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x) := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  obtain ⟨s, hs, hts⟩ := (mem_noncompactPart_iff hu l _).1 (inP_jK (K := K) (ι_mem_pow ht))
  rw [← algebraMap_smul K, map_smul, Pi.smul_apply, smul_eq_mul, hx', hts]
  have e1 : jK (ι π₀) ^ l * s * ((gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x)) i =
      s * ∑ j, (jK (ι π₀) ^ l * (gramK h b)⁻¹ i j) * (gramK h b *ᵥ b.equivFun x) j := by
    conv_lhs => rw [mulVec, dotProduct]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1]
  exact (SP K 𝔭).mul_mem hs ((SP K 𝔭).sum_mem fun j _ => (SP K 𝔭).mul_mem (hl (i, j)) (hv j))
end Formalism.HermitianLattices.Ext.L3.HU
