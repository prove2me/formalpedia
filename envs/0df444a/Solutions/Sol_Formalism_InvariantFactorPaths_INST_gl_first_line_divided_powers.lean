-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.gl_first_line_divided_powers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:47.815917+00:00
-- url     : https://prove2.me/submissions/79d9c2ef-d938-4a62-9b1a-4b01850346f1

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_C
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_C_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_C_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_E
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_div_X
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
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_mul
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_glAct_C__ff1861139e62
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : RowGlDiv := by
  intro p _ r n ν a b hab k f
  rw [rgl_E]
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    rw [rgl_swp_C]
    match k with
    | 0 => simp [rgl_rowDiv_C_zero, rgl_swp_C]
    | k + 1 =>
      rw [rgl_rowDiv_C_succ, pow_succ, Module.End.mul_apply, glAct_C', map_zero, map_zero, smul_zero]
  | add f g hf hg => rw [rowDiv_add, map_add, map_add, map_add, smul_add, hf, hg]
  | mul_X f v hf =>
    rw [rgl_rowDiv_mul, map_mul, divPow_mul _ (Formalism.GM.M.FB.glAct_mul (vecL ν) n a b), map_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [map_mul, hf, rgl_div_X ν a b hab]
end Formalism.InvariantFactorPaths.INST
