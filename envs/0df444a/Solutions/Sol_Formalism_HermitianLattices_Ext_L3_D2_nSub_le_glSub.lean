-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nSub_le_glSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:22.09195+00:00
-- url     : https://prove2.me/submissions/32623a63-f6fb-4fa3-99cc-c6597a730507

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_endL_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_glSub_of_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_anti


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
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 A₀) 𝔭 k ≤ glSub (locF 𝔭 B₀) := by
  obtain ⟨r, hr⟩ := exists_endL_le hA₀ hB₀ h𝔭
  refine ⟨1 + r, fun k hk X hX => mem_glSub_of_sub_mem hB₀ h𝔭 fun y hy => ?_⟩
  have h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀) :=
    fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)
  have := hr 1 h1 y hy
  rwa [pow_one] at this
end Formalism.HermitianLattices.Ext.L3.D2
