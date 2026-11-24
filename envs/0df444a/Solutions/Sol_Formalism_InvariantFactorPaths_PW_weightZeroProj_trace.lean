-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weightZeroProj_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:20.720885+00:00
-- url     : https://prove2.me/submissions/5893840d-1a10-48ef-8ef3-59d8e737ff9f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_scalar_projection_apply
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G₁ : GlW K U n) (S : Finset (Fin n → ℤ)) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0) (φ : U →ₗ[K] U) :
    LinearMap.trace K U (pr0 G₁ G₁ S φ) = LinearMap.trace K U φ := by
  classical
  have hsum : ∑ ν ∈ S, G₁.comp ν = 1 := by
    ext x
    simpa using G₁.sum_comp x S (hS x)
  have hidem : ∀ ν, G₁.comp ν * G₁.comp ν = G₁.comp ν := by
    intro ν
    ext x
    simp [G₁.idem]
  have hp : pr0 G₁ G₁ S φ = ∑ ν ∈ S, G₁.comp ν * (φ * G₁.comp ν) := by
    ext x
    simp [scalar_projection_apply]
  rw [hp, map_sum]
  calc ∑ ν ∈ S, LinearMap.trace K U (G₁.comp ν * (φ * G₁.comp ν))
      = ∑ ν ∈ S, LinearMap.trace K U (φ * G₁.comp ν) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [LinearMap.trace_mul_comm, mul_assoc, hidem ν]
    _ = LinearMap.trace K U φ := by
        rw [← map_sum, ← Finset.mul_sum, hsum, mul_one]
end Formalism.InvariantFactorPaths.PW
