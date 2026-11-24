-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_isom_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:04.717249+00:00
-- url     : https://prove2.me/submissions/f2f9eb7a-5153-4cd5-b44f-7de914b9311e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_E
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_eq_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_Z
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ent_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_sum_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_equivOfMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivOfMatrix_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isUnif0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_unitary_near
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gmap_equivOfMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_conjTranspose
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isLocUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_noncompactPart_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_smul_locF_iff_repr
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
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩ := exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh
    (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  refine ⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU),
    gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩
  rw [mem_smul_locF_iff_repr]
  intro l
  have hb1 : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]
  show InP 𝔭 (k - e) (G l i - jK (Y l i))
  rw [hGX, mem_noncompactPart_iff hu]
  refine ⟨D l i, hD l i, ?_⟩
  simp
end Formalism.HermitianLattices.Ext.L3.HU
