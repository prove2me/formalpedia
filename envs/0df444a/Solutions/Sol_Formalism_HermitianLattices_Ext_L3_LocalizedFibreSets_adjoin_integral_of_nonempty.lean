-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.adjoin_integral_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:17.211219+00:00
-- url     : https://prove2.me/submissions/b2f249d5-e8cf-4f53-867d-cd3fcaf61114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinIntegralOfNonempty
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_adjoin_le_of_mem_fibSet
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
private theorem star_algebraMap_of_fixed_field_eq (hF : IsFixF K F) (t : 𝓞 F) :
    star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
  rw [hF]
  refine ⟨(t : F), ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  first
  | rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl
  | simp
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
end
end

set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (fibSet S L 𝔭.1 Λ').Nonempty) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ') := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  intro 𝔭
  obtain ⟨Λ, hΛ⟩ := H 𝔭
  have hle := adjoin_le_of_mem_fibSet S hΛ
  obtain ⟨-, ⟨g, hg, hgΛ⟩, -, -⟩ := hΛ
  have hp : 𝔭.1.IsPrime := 𝔭.2.isPrime
  rw [← hgΛ] at hle
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 (hle hx)
  obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (hle hy)
  rw [LocF.mem_locF_iff hp] at hx' hy'
  rw [LocF.mem_locF_iff hp]
  obtain ⟨t, ht, htx⟩ := hx'
  obtain ⟨s, hs, hsy⟩ := hy'
  refine ⟨t * s, fun hts => (hp.mem_or_mem hts).elim ht hs, ?_⟩
  have key := hLi _ htx _ hsy
  have e1 : h (g x') (g y') = h x' y' := hg x' y'
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [e1]
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x',
    ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) y'] at key
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, starRingEnd_apply,
    star_algebraMap_of_fixed_field_eq hF] at key
  convert key using 1
  rw [Algebra.smul_def, map_mul, map_mul, smul_eq_mul, smul_eq_mul]
  simp only [RingHom.id_apply]
  ring
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
