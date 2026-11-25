-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_near_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:54.654669+00:00
-- url     : https://prove2.me/submissions/7b715dee-6425-4148-bcb4-cf840a8a8ed2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exact_step
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_divK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_inL_zero_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n s : 𝓞 F} {b : V}
    (hb : h b b = κ (ι n)) (hsb : ι s • b ∈ A) {v k : ℕ} {x : V} (hx : InL 𝔭 A 0 x)
    (hε : InI 𝔭 (v + k) (h x x - κ (ι n)))
    (hD : ¬ InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))) :
    ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hd : h (x - b) (x - b) ≠ 0 := by
    intro h0
    apply hD
    rw [h0, mul_zero]
    exact InI.zero hp _
  have hs0 : κ (ι s) ≠ 0 := by
    intro h0
    apply hD
    rw [map_mul, map_mul, h0, zero_mul, zero_mul]
    exact InI.zero hp _
  obtain ⟨h1, h2⟩ := exact_step hs hd
  set y := b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b) with hy
  set w := x - b with hw
  have hsw : InL 𝔭 A 0 (ι s • w) := by
    rw [hw, smul_sub]
    refine InL.sub hp ?_ ((inL_zero_iff hp).2 (le_locF 𝔭 A hsb))
    rw [← algebraMap_smul K (ι s)]
    have := InL.smul hp (InI.int hp (ι s)) hx
    rwa [zero_add] at this
  have hDe : h (ι s • w) (ι s • w) = κ (ι (s * s)) * h w w := form_smul hF h s s w w
  have hD0 : InI 𝔭 0 (κ (ι (s * s)) * h w w) := by
    rw [← hDe]
    exact InL.form hp hF hA hsw hsw
  have hDs : star (κ (ι (s * s)) * h w w) = κ (ι (s * s)) * h w w := by
    rw [← hDe]; exact hs.eq _ _
  have h3 : InI 𝔭 (v + k) (κ (ι s) * (h x x - κ (ι n))) := by
    have := InI.mul hp (InI.int hp (ι s)) hε
    rwa [zero_add] at this
  have h4 := InI.divK h𝔭 hF hDs hD0 hD h3
  have h5 := InL.smul hp h4 hsw
  rw [add_zero] at h5
  have h6 : InL 𝔭 A k (y - x) := by
    rw [h2, hb]
    apply InL.neg
    have : ((h w w)⁻¹ * (h x x - κ (ι n))) • w =
        ((κ (ι (s * s)) * h w w)⁻¹ * (κ (ι s) * (h x x - κ (ι n)))) • ι s • w := by
      rw [← algebraMap_smul K (ι s), smul_smul]
      congr 1
      rw [map_mul, map_mul]
      field_simp
    rw [this]
    exact h5
  refine ⟨y, ?_, h1.trans hb, h6⟩
  have : y = x + (y - x) := by abel
  rw [this]
  exact hx.add hp (h6.mono (Nat.zero_le _))
end Formalism.HermitianLattices.Ext.L3.Cell
