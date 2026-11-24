-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.form_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:41.914824+00:00
-- url     : https://prove2.me/submissions/da4236d5-a178-4a58-9a72-119850024c7d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {i j : ℕ} {x y : V}
    (hx : x ∈ extP K 𝔭 ^ i • locF 𝔭 A₀) (hy : y ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    h x y ∈ pK K 𝔭 (i + j) := by
  have := h𝔭.isPrime
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨x', hx', rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨y', hy', rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hy
  obtain ⟨t, ht, hx''⟩ := (LocalSpans.mem_locF 𝔭 A₀ x').1 hx'
  obtain ⟨s, hs, hy''⟩ := (LocalSpans.mem_locF 𝔭 A₀ y').1 hy'
  have h0 : h x' y' ∈ pK K 𝔭 0 := by
    obtain ⟨w, hw⟩ := hA₀i _ hx'' _ hy''
    refine (mem_pK h𝔭).2 ⟨t * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht hs, w, by simp, ?_⟩
    rw [localizedQuotients.form_smul hF, MeanB.algebraMap_comp] at hw
    rw [← hw]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
    star_pow, MeanB.star_algebraMap hF, ← mul_assoc, ← pow_add, add_comm j i]
  exact (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨_, h0, rfl⟩
end Formalism.HermitianLattices.Ext.L3.D2
