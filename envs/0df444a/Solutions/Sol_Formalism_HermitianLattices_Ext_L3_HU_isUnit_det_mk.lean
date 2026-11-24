-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.isUnit_det_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:17.984364+00:00
-- url     : https://prove2.me/submissions/776e9f71-7b13-4b7f-9421-079eb71a6254

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_E
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_eq_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_Z
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ent_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_det_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isUnif0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_conjTranspose
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isLocUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_jK_inj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) Y.det) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨h0, h1⟩ := det_unit (isLocUnif hK hF h𝔭 hu) hHh (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  have hdet : (Y.map jK).det = jK Y.det := by
    have := RingHom.map_det jK Y
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  rw [hdet] at h0 h1
  obtain ⟨t, ht, z, e1⟩ := mem_SP.1 h1
  have e2 : z * Y.det = ι t := by
    apply jK_inj
    rw [map_mul, e1]
    field_simp
  obtain ⟨u, hu'⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht N
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (ι u * z))
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ N)), Ideal.Quotient.eq]
  have : Y.det * (ι u * z) - 1 = ι (u * t - 1) := by
    rw [map_sub, map_mul, map_one, ← e2]
    ring
  rw [this]
  exact ι_mem_pow hu'
end Formalism.HermitianLattices.Ext.L3.HU
