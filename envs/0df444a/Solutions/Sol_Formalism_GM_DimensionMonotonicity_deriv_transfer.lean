-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.deriv_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:28.67779+00:00
-- url     : https://prove2.me/submissions/448fc827-d0a6-4724-8068-5e8a8907bbad

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {K σ τ : Type} [CommRing K] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (D0 : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (D1 : MvPolynomial τ K →ₗ[K] MvPolynomial τ K)
    (h0 : ∀ x y, D0 (x * y) = x * D0 y + y * D0 x) (h1 : ∀ x y, D1 (x * y) = x * D1 y + y * D1 x)
    (hg : ∀ v, D1 (φ (X v)) = φ (D0 (X v))) (f : MvPolynomial σ K) : D1 (φ f) = φ (D0 f) := by
  have hD0one : D0 1 = 0 := by simpa using h0 1 1
  have hD1one : D1 1 = 0 := by simpa using h1 1 1
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [C_eq_smul_one, map_smul φ, map_one φ, map_smul D1, map_smul D0, hD1one, hD0one, smul_zero, smul_zero,
      map_zero]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    rw [map_mul φ, h1, hg v, hp, h0, map_add φ, map_mul φ, map_mul φ]
end Formalism.GM.DimensionMonotonicity
