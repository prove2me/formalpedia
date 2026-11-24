-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:00.911047+00:00
-- url     : https://prove2.me/submissions/8a034778-5421-42a5-be1d-54d8f73ded10

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_star_mem_pK
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
open NO
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (z : K) :
    nO 𝔭 (star z) = nO 𝔭 z := by
  have hs : ∀ a : K, star a ∈ pK K 𝔭 0 ↔ a ∈ pK K 𝔭 0 := fun a =>
    ⟨fun h => by simpa using star_mem_pK hF h𝔭 h, star_mem_pK hF h𝔭⟩
  have h1 : (pK K 𝔭 0).toAddSubgroup.map (starAddEquiv : K ≃+ K).toAddMonoidHom =
      (pK K 𝔭 0).toAddSubgroup := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact star_mem_pK hF h𝔭 hb
    · intro ha
      exact ⟨star a, star_mem_pK hF h𝔭 ha, star_star a⟩
  have h2 : (zR 𝔭 z).map (starAddEquiv : K ≃+ K).toAddMonoidHom = zR 𝔭 (star z) := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨star b, star_mem_pK hF h𝔭 hb, (star_mul' z b).symm⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨z * star b, ⟨star b, star_mem_pK hF h𝔭 hb, rfl⟩, ?_⟩
      show star (z * star b) = star z * b
      rw [star_mul', star_star]
  have h3 := AddSubgroup.relIndex_map_map_of_injective (zR 𝔭 z) (pK K 𝔭 0).toAddSubgroup
    (f := (starAddEquiv : K ≃+ K).toAddMonoidHom) (starAddEquiv : K ≃+ K).injective
  rw [h1, h2] at h3
  exact h3
end Formalism.HermitianLattices.Ext.L3.D2
