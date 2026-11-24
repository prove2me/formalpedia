-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.redCount_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:17.674326+00:00
-- url     : https://prove2.me/submissions/10f1014d-6560-436c-a4f5-3ca73bad9e6d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_map_factor_map_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_mem_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_cmb_single
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_inA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_eL_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_end_apply_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isom_matrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_map_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_matrix_of_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_form_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_smul_mono_pow


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
theorem _root_.solution [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c j : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hj : 1 ≤ j) :
    redCount h (locF 𝔭 (spanO b)) 𝔭 j = Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
      ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
        X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} := by
  have := h𝔭.isPrime
  have hF : IsFixF K F := hFF.out
  unfold redCount
  refine Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)
  constructor
  · rintro ⟨g, hg, hgX⟩
    obtain ⟨Y, hY1, hY2⟩ := exists_matrix_of_isom hF b hH h𝔭 hg (j + c)
    refine ⟨Y.map (Ideal.Quotient.mk _), (mk_form_iff 𝔭 _ H Y).2 hY1, ?_⟩
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff]
    intro i
    obtain ⟨y, hy1, hy2⟩ := hgX (inA 𝔭 b (cmb b (Pi.single i 1)))
    rw [hy2, mk_eq_iff, hy1, coe_inA, coe_cmb_single, coe_inA, coe_cmb]
    exact smul_mono_pow (Nat.le_add_right j c) (hY2 i)
  · rintro ⟨X', hX', hmap⟩
    obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X'
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff] at hmap
    obtain ⟨g, hg, hgY⟩ := exists_isom_matrix hK hF hs hd b hH h𝔭 he (by omega : c + 1 ≤ j + c) Y
      ((mk_form_iff 𝔭 _ H Y).1 hX')
    rw [Nat.add_sub_cancel] at hgY
    refine ⟨g, hg, fun x => ⟨⟨g x, aut_mem hg x.2⟩, rfl, ?_⟩⟩
    obtain ⟨c₀, hc⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk x)
    rw [hc, end_apply_cmb b j X Y hmap c₀, mk_eq_iff]
    rw [mk_eq_iff] at hc
    have e1 : (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) =
        -(g ((x : V) - (inA 𝔭 b (cmb b c₀) : V)) + (g (cmb b c₀ : V) - (cmb b (Y *ᵥ c₀) : V))) := by
      rw [map_sub, coe_inA, coe_inA]
      abel
    show (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) ∈ _
    rw [e1]
    exact neg_mem (add_mem (aut_mem_smul hg _ hc) (aut_cmb b hgY c₀))
end Formalism.HermitianLattices.Ext.L3.HU
