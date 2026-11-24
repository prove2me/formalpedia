-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.gl_one_first_line_action
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.7979+00:00
-- url     : https://prove2.me/submissions/08be29bb-bc0e-43e8-b528-e77c6970170d

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_X
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_C
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_C_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_X_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_X_one
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_E
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_glAct_X
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
theorem _root_.solution : RowGlOne := by
  intro p _ r n ν a b f
  rw [rgl_E]
  induction f using MvPolynomial.induction_on with
  | C c => rw [rgl_rowDiv_C_succ, rgl_swp_C, glAct_C', map_zero]
  | add f g hf hg => rw [rowDiv_add, map_add, map_add, map_add, hf, hg]
  | mul_X f v hf =>
    obtain ⟨c, s⟩ := v
    have h1 : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
    rw [rgl_rowDiv_mul, h1, Finset.sum_pair (by decide), rgl_rowDiv_zero, rgl_rowDiv_X_zero, rgl_rowDiv_X_one,
      map_add, map_mul, map_mul, map_mul, hf, Formalism.GM.M.FB.glAct_mul, rgl_swp_X, rgl_glAct_X]
    split_ifs <;> simp [rgl_swp_X, mul_comm]
end Formalism.InvariantFactorPaths.INST
