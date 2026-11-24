-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.congrP_add_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:44.904929+00:00
-- url     : https://prove2.me/submissions/e58acd08-74be-4d31-8064-5265a1721863

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_form_right_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_form_left_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_congrP_algebraMap_iff_sub_mem
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
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) {c : K}
    (hc : CongrP 𝔭 k (h y y) c) : CongrP 𝔭 k (h (y + z) (y + z)) c := by
  rw [D2.congrP_algebraMap_iff_sub_mem h𝔭] at hc ⊢
  have hzA : z ∈ A := Submodule.smul_le_right hz
  have e : h (y + z) (y + z) - c = (h y y - c) + h y z + h z y + h z z := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [e]
  exact add_mem (add_mem (add_mem hc (form_right_mem h𝔭 hA hAi hy hz))
    (form_left_mem hF h𝔭 hA hAi hy hz)) (form_right_mem h𝔭 hA hAi hzA hz)
end Formalism.HermitianLattices.Ext.L3.LIOrb
