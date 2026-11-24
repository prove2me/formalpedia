-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.vec_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:56.504801+00:00
-- url     : https://prove2.me/submissions/b2cd025c-e30a-4a99-bc9e-c6b4c6723399

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_eta
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_last
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_last
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (n : Fin T.t → ℕ) (m0 : ℕ) (a : Fin (T.pos i + 1 + 1)) :
    LL.vec (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc m0).vec a := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_vec_last]
    have : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]; exact vec_eta LL T hadm i _
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_vec_castSucc]
    have : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]
    simp [Letters.takeD, Letters.setTies, (by omega : (a : ℕ) < N)]
end Formalism.GM.DimensionMonotonicity
