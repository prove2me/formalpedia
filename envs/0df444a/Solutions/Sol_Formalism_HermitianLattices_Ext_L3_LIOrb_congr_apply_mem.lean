-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.congr_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:45.554557+00:00
-- url     : https://prove2.me/submissions/76de37d5-fb90-4a14-9bf9-522585eaec08

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_pow_smul_anti
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  have hz1 : algebraMap F K (π : F) ^ r₂ • z ∈ locF 𝔭 M₁ :=
    h2 ((D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).2 ⟨z, hz, rfl⟩)
  have h3 := pow_smul_anti 𝔭 (locF 𝔭 M₁) hj (hg _ hz1)
  rw [pow_add, Submodule.mul_smul] at h3
  have h4 := Submodule.smul_mono (le_refl (extP K 𝔭 ^ r₂)) h1 h3
  obtain ⟨w, hw, e⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).1 h4
  rw [map_smul, ← smul_sub] at e
  have e' : g z - z = w :=
    smul_right_injective V (pow_ne_zero r₂ (D2.unif_ne_zero (K := K) hπ')) e
  have : g z = w + z := by rw [← e']; abel
  rw [this]
  exact add_mem hw hz
end Formalism.HermitianLattices.Ext.L3.LIOrb
