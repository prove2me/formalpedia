-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCB.mem_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:39.784957+00:00
-- url     : https://prove2.me/submissions/baf9eaba-332d-4392-8d07-a9d2bdcccad4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCB
open WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCB
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2
end Formalism.HermitianLattices.Ext.L3.WCB
