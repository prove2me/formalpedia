-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.form_left_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:47.130195+00:00
-- url     : https://prove2.me/submissions/1a44ec05-6bb0-48b4-9768-f728c695d60f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_locF_one_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_pow_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A)
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) :
    h z y ∈ D2.pK K 𝔭 k := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  rw [← hA] at hz
  obtain ⟨w, hw, rfl⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' A).1 hz
  rw [hA] at hw
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_pow,
    MeanB.star_algebraMap hF]
  have h1 := hAi w hw y hy
  rw [D2.locF_one_eq] at h1
  simpa using D2.mul_mem_pK h𝔭 (D2.unif_pow_mem_pK (K := K) hπ k) h1
end Formalism.HermitianLattices.Ext.L3.LIOrb
