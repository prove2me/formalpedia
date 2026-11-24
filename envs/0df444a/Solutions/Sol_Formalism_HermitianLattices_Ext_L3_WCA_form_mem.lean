-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.form_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:39.705983+00:00
-- url     : https://prove2.me/submissions/df468905-bc0c-4613-9cc4-eed9d7636d68

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_form_mem_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_form_mem_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {i k : ℕ} {p q : V} (hp : p ∈ extP K 𝔭 ^ i • A) (hq : q ∈ extP K 𝔭 ^ k • A) :
    ∃ z ∈ extP K 𝔭 ^ (i + k), κ z = h p q := by
  induction hp using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨r, hr, e⟩ := form_mem_right hA hm hq
    refine ⟨conjO K a * r, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul (conjO_mem_pow hF 𝔭 i a ha) hr
    · rw [← algebraMap_smul K a, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, e]
      rfl
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [map_add, map_add, LinearMap.add_apply, e, f]⟩
end Formalism.HermitianLattices.Ext.L3.WCA
