-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_equiv_of_mem_endL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:13.604175+00:00
-- url     : https://prove2.me/submissions/70137a83-18bd-4b02-862f-4b8d709ba726

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_eq_zero_of_forall_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_of_add_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_glSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pow_zero_smul


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) :
    ∃ X : V ≃ₗ[K] V, (∀ x, X x = x + D x) ∧ X ∈ glSub (locF 𝔭 A₀) := by
  have hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w + D w = 0 := hw
    exact eq_zero_of_forall_mem hA₀ h𝔭 fun j =>
      mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
  · have hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x := fun x => by
      rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
    rw [mem_glSub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _
      rw [hX]
      exact add_mem hx (Submodule.smul_le_right (hD x hx))
    · intro y hy
      refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      have h1 := hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      have := mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y)
        (by rw [← h1, pow_zero_smul]; exact hy)
      rwa [pow_zero_smul] at this
end Formalism.HermitianLattices.Ext.L3.D2
