-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_isom_lift_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:32.184122+00:00
-- url     : https://prove2.me/submissions/e2c3461d-92af-4e45-b6e4-1733897d3540

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_inP_jK_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_smul_mono_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_mem_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_matrix_of_end
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_inA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_congrP_iff_inP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_end_apply_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isom_matrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_col
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (X : Module.End (𝓞 K) (QA 𝔭 b k))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 (spanO b)), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ x x' : ↥(locF 𝔭 (spanO b)),
      Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - e) • (locF 𝔭 (spanO b)) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨Y, hXY⟩ := exists_matrix_of_end h𝔭 b k X
  have hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by
    intro i j
    have h1 := hX _ _ _ _ (hXY i).symm (hXY j).symm
    rw [congrP_iff_inP, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← form_col,
      form_single, ← map_sub, inP_jK_iff h𝔭] at h1
    exact h1
  obtain ⟨g, hg, hgY⟩ := exists_isom_matrix hK hF hs hd b hH h𝔭 he hk Y hY
  refine ⟨g, hg, fun x x' hxx' => ?_⟩
  obtain ⟨c, hc⟩ := exists_cmb h𝔭 b k (Submodule.Quotient.mk x)
  rw [hc, end_apply_cmb b k X Y hXY c, mk_eq_iff] at hxx'
  rw [mk_eq_iff] at hc
  have e1 : g (x : V) - x' = g ((x : V) - (inA 𝔭 b (cmb b c) : V)) +
      (g (cmb b c : V) - (cmb b (Y *ᵥ c) : V)) - ((x' : V) - (inA 𝔭 b (cmb b (Y *ᵥ c)) : V)) := by
    rw [map_sub, coe_inA, coe_inA]
    abel
  rw [e1]
  exact sub_mem (add_mem (smul_mono_pow (Nat.sub_le k e) (aut_mem_smul hg _ hc)) (aut_cmb b hgY c))
    (smul_mono_pow (Nat.sub_le k e) hxx')
end Formalism.HermitianLattices.Ext.L3.HU
