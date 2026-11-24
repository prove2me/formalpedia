-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.sigmaCount_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:58.399318+00:00
-- url     : https://prove2.me/submissions/4fe659ef-5c22-4f54-bd61-293619b0255e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_sigma_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_skew_mulVec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_inA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_congrP_iff_inP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_eL_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_end_apply_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_matrix_of_end
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_congr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_inP_jK_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_single


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
theorem _root_.solution [hFF : Fact (IsFixF K F)] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) :
    sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j = Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
      Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by
  have := h𝔭.isPrime
  have hF : IsFixF K F := hFF.out
  unfold sigmaCount
  refine Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)
  obtain ⟨Y, hXY⟩ := exists_matrix_of_end h𝔭 b j X
  rw [(eL_eq_iff h𝔭 b j X Y).2 hXY, mk_sigma_iff]
  constructor
  · intro hX i l
    have h1 := hX _ _ _ _ (end_apply_cmb b j X Y hXY (Pi.single i 1)).symm
      (end_apply_cmb b j X Y hXY (Pi.single l 1)).symm
    rw [congrP_iff_inP, sub_zero, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH,
      ← map_add, skew_mulVec, form_single, inP_jK_iff h𝔭] at h1
    exact h1
  · intro hY x y x' y' hx hy
    obtain ⟨c, hc⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk x)
    obtain ⟨c', hc'⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk y)
    rw [hc, end_apply_cmb b j X Y hXY c, mk_eq_iff] at hx
    rw [hc', end_apply_cmb b j X Y hXY c', mk_eq_iff] at hy
    rw [mk_eq_iff] at hc hc'
    rw [congrP_iff_inP, sub_zero]
    have h1 := form_congr hF b hH (inA 𝔭 b (cmb b (Y *ᵥ c))).2 y.2 hx hc'
    have h2 := form_congr hF b hH (inA 𝔭 b (cmb b c)).2 y'.2 hc hy
    have h3 : InP 𝔭 j (h (inA 𝔭 b (cmb b (Y *ᵥ c)) : V) (inA 𝔭 b (cmb b c') : V) +
        h (inA 𝔭 b (cmb b c) : V) (inA 𝔭 b (cmb b (Y *ᵥ c')) : V)) := by
      rw [coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← map_add, skew_mulVec,
        inP_jK_iff h𝔭]
      exact form_mem hY _ _
    have := (h1.add h2).add h3
    convert this using 1
    ring
end Formalism.HermitianLattices.Ext.L3.HU
