-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_freeze_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:11.705685+00:00
-- url     : https://prove2.me/submissions/0f90f906-6c1b-4daa-bee7-494937198f4a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_deriv_transfer
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pow_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freezeSub_gen
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
import Theorems.Thm_Formalism_GM_M_FB_glAct_X
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
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
theorem _root_.solution (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (f : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (K + 1) a b (freeze p LL ρ n f) = freeze p LL ρ n (glAct p LL K a b f) := by
  unfold freeze
  rw [Formalism.GM.M.FB.glAct_mul]
  have hX : glAct p (LL.snoc n) (K + 1) a b (X (Fin.last K, ρ)) = 0 := by
    rw [Formalism.GM.M.FB.glAct_X]; simp [Ne.symm ha]
  rw [glAct_pow_zero _ _ _ _ hX, mul_zero, add_zero]
  congr 1
  exact deriv_transfer (aeval (freezeSub p LL ρ)) (glAct p LL K a b) (glAct p (LL.snoc n) (K + 1) a b)
    (fun x y => Formalism.GM.M.FB.glAct_mul LL K a b x y) (fun x y => Formalism.GM.M.FB.glAct_mul (LL.snoc n) (K + 1) a b x y)
    (fun v => by rw [aeval_X]; exact glAct_freezeSub_gen LL n ρ a b ha hb v) f
end Formalism.GM.DimensionMonotonicity
