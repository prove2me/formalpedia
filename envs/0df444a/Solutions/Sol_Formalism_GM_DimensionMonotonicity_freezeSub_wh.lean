-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.freezeSub_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:09.781065+00:00
-- url     : https://prove2.me/submissions/cc96f264-4a05-4250-9276-d24f4763a621

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_snoc_castSucc
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_snoc_last
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters K) (n : ℕ) (ρ : Fin r) (v : Fin K × Fin r) :
    IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (freezeSub p LL ρ v) (wv LL K v - Pi.single ρ 1) := by
  classical
  obtain ⟨i, c⟩ := v
  have hX : ∀ x, IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (X x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
      (wv (LL.snoc n) (K + 1) x) := fun x => isWeightedHomogeneous_X _ _ x
  have hwi : ∀ c : Fin r, wv LL K (i, c) = if LL.vec i then Pi.single c 1 else -Pi.single c 1 := by
    intro c; simp [wv, i.isLt]
  by_cases h1 : LL.vec i
  · by_cases h2 : c = ρ
    · subst h2
      simp only [freezeSub, h1, if_true]
      apply IsWeightedHomogeneous.sum
      intro c' _
      have := (hX (Fin.castSucc i, c')).mul (hX (Fin.last K, c'))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_pos h1] at this
      convert this using 1
      rw [hwi, if_pos h1]; abel
    · simp only [freezeSub, h1, h2, if_true, if_false]
      have := (hX (Fin.last K, ρ)).mul (hX (Fin.castSucc i, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_pos h1] at this
      convert this using 1
      rw [hwi, if_pos h1]; abel
  · by_cases h2 : c = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, if_false, Bool.false_eq_true]
      have := (hX (Fin.last K, c)).mul (hX (Fin.castSucc i, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_neg h1] at this
      convert this using 1
      rw [hwi, if_neg h1]; abel
    · simp only [freezeSub, h1, h2, if_true, if_false, Bool.false_eq_true]
      have e1 := (hX (Fin.last K, ρ)).mul (hX (Fin.castSucc i, c))
      have e2 := (hX (Fin.castSucc i, ρ)).mul (hX (Fin.last K, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_neg h1] at e1 e2
      rw [← mem_weightedHomogeneousSubmodule] at e1 e2 ⊢
      have e3 := Submodule.sub_mem _ e1 (show _ ∈ weightedHomogeneousSubmodule ℚ_[p] (wv (LL.snoc n) (K + 1))
        (-Pi.single ρ 1 + -Pi.single c 1) from by convert e2 using 2; try abel)
      convert e3 using 2
      rw [hwi, if_neg h1]; abel
end Formalism.GM.DimensionMonotonicity
