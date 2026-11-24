-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.QQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:50.48387+00:00
-- url     : https://prove2.me/submissions/eeed1d0b-2dbf-48b8-ad2d-5d89df2d0f9c

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_weight
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_apply
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
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
theorem _root_.solution (hHom : HomInv) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) {W : Submodule K V} (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l)
    (h0 : ∀ ψ : U →ₗ[K] V, (∀ a b x, ψ (G₁.E a b x) = G₂.E a b (ψ x)) → (∀ x, ψ x ∈ W) → ψ = 0)
    {m : V} (hm : m ∈ W) : QQ G₁ G₂ S l b m = 0 := by
  rw [QQ_apply]
  have hWg : G₂.Graded W := G₂.graded_of hW
  have hz : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) = 0 := by
    intro i
    have hφW : ∀ x, pr0 G₁ G₂ S ((b.coord i).smulRight m) x ∈ W := fun x =>
      weightZeroProj_mem G₁ G₂ S hWg (fun y => by rw [LinearMap.smulRight_apply]; exact W.smul_mem _ hm) x
    obtain ⟨h1, h2, -⟩ := hHom K U V n G₁ G₂ W l hW hb _ hφW (weightZeroProj_weight G₁ G₂ S _)
    exact h0 _ h1 h2
  simp [hz]
end Formalism.InvariantFactorPaths.PW
