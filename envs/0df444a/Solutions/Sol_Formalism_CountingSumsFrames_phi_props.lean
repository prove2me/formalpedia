-- Prove2me | solution 1 for Formalism.CountingSumsFrames.phi_props
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:41.726439+00:00
-- url     : https://prove2.me/submissions/162cf886-000d-4089-89c5-a7f0d0047329

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_psi_mem
import Theorems.Thm_Formalism_CountingSumsFrames_psi_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_psi_comp
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) (j0 : ℕ)
    (π : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hπP : ∀ x ∈ Pol p r (Lz L j0), π x ∈ Pol p r (Lz L j0))
    (hπE : ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π (glAct p L j0 c d x) = glAct p L j0 c d (π x))
    (hπc : ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π x)) :
    (∀ c d x, (π ∘ₗ psi p L j0) (glAct p L j0 c d x) = glAct p L j0 c d ((π ∘ₗ psi p L j0) x)) ∧
    (∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
      (π ∘ₗ psi p L j0) x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) ∧
    (∀ x, (π ∘ₗ psi p L j0) x ∈ Pol p r (Lz L j0)) := by
  refine ⟨fun c d x => ?_, fun ν x hx => ?_, fun x => hπP _ (psi_mem L j0 x)⟩
  · simp only [LinearMap.comp_apply]
    rw [psi_glAct, hπE _ (psi_mem L j0 x)]
  · have e : (GA p L j0).comp ν x = x := by
      show weightedHomogeneousComponent (wv L j0) ν x = x
      rw [weightedHomogeneousComponent_of_mem hx, if_pos rfl]
    simp only [LinearMap.comp_apply]
    rw [← e, psi_comp, hπc _ (psi_mem L j0 x)]
    exact weightedHomogeneousComponent_mem _ _ _
end Formalism.CountingSumsFrames
