-- Prove2me | solution 1 for Formalism.CountingSumsFrames.mul_ltr_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:21.38995+00:00
-- url     : https://prove2.me/submissions/6fb0421c-5095-4e81-838b-15a1e5c0b85b

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_wL
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
import Theorems.Thm_Formalism_GM_M_FB_weight_wL
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
theorem _root_.solution (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by
  rw [pol_iff] at hg ⊢
  have hq : IsWeightedHomogeneous (wL N r) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p]))
      (Finsupp.weight (wL N r) (ltr (fsj N r j0) m')) := isWeightedHomogeneous_monomial _ _ _ rfl
  convert hg.mul hq using 1
  funext i
  rw [Pi.add_apply, weight_wL]
  by_cases h : (i : ℕ) < j0
  · have e : ∑ c, ((ltr (fsj N r j0) m' (i, c) : ℕ) : ℤ) = 0 := Finset.sum_eq_zero fun c _ => by
      rw [ltr, Finsupp.filter_apply, if_neg (by simp [fsj]; omega)]; simp
    rw [e, add_zero]; simp [Lz, h]
  · have e : ∑ c, ((ltr (fsj N r j0) m' (i, c) : ℕ) : ℤ) = L.deg i := by
      rw [← hm i]; push_cast
      exact Finset.sum_congr rfl fun c _ => by rw [ltr, Finsupp.filter_apply, if_pos (by simp [fsj]; omega)]
    rw [e]; simp [Lz, h]
end Formalism.CountingSumsFrames
