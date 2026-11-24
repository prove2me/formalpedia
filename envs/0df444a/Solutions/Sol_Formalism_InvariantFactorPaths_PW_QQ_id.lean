-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.QQ_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:50.013351+00:00
-- url     : https://prove2.me/submissions/6726fd9d-7b2e-4800-ac43-1b4d3a279de5

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_weight
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_comm2
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_trace
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_apply
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_postcomp
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
theorem _root_.solution (hNat : InvNat) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0)
    (hSch : ∀ φ : U →ₗ[K] U, (∀ c, homAct G₁.E G₁.E c c φ = 0) →
      InvOp (homAct G₁.E G₁.E) l (List.finRange n) φ = (LinearMap.trace K U φ / (k : K)) • LinearMap.id)
    (hk : k ≠ 0) (θ : U →ₗ[K] V) (hθ : ∀ a b x, θ (G₁.E a b x) = G₂.E a b (θ x)) (y : U) :
    QQ G₁ G₂ S l b (θ y) = θ y := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hθc : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x) := fun μ x =>
    comp_comm2 G₁ G₂ θ (fun c x => hθ c c x) μ x
  let θ' : (U →ₗ[K] U) →ₗ[K] (U →ₗ[K] V) :=
    { toFun := fun χ => θ ∘ₗ χ
      map_add' := fun χ ψ => by ext x; simp
      map_smul' := fun c χ => by ext x; simp }
  have hθ'a : ∀ χ, θ' χ = θ ∘ₗ χ := fun χ => rfl
  have hcomm : ∀ a b χ, θ' (homAct G₁.E G₁.E a b χ) = homAct G₁.E G₂.E a b (θ' χ) := fun a b χ => by
    rw [hθ'a, hθ'a]
    exact homAct_postcomp G₁.E G₁.E G₂.E θ hθ a b χ
  have htr : ∀ i, LinearMap.trace K U ((b.coord i).smulRight y) = b.coord i y := by
    intro i
    rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
    simp [LinearMap.toMatrix_apply, Finsupp.single_apply]
    simp [Matrix.vecMulVec_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have key : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight (θ y)) (b i) = (b.coord i y / (k : K)) • θ (b i) := by
    intro i
    have h1 : (b.coord i).smulRight (θ y) = θ' ((b.coord i).smulRight y) := by
      ext x
      simp [hθ'a]
    have h2 : Psi G₁ G₂ S l (θ' ((b.coord i).smulRight y)) =
        θ' (InvOp (homAct G₁.E G₁.E) l (List.finRange n) (pr0 G₁ G₁ S ((b.coord i).smulRight y))) := by
      have hp : pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y)) = θ' (pr0 G₁ G₁ S ((b.coord i).smulRight y)) :=
        weightZeroProj_comp G₁ G₂ S θ hθc _
      show InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y))) = _
      rw [hp]
      exact (hNat K _ _ (Fin n) (homAct G₁.E G₁.E) (homAct G₁.E G₂.E) θ' hcomm l (List.finRange n) _).symm
    rw [h1, h2, hSch _ (weightZeroProj_weight G₁ G₁ S _), weightZeroProj_trace G₁ S hS, hθ'a, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, htr]
  have hsc : ∀ i, (k : K) • ((b.coord i y / (k : K)) • θ (b i)) = θ (b.repr y i • b i) := by
    intro i
    have hc : (k : K) * (b.coord i y / (k : K)) = b.repr y i := by
      rw [Module.Basis.coord_apply]
      field_simp
    rw [smul_smul, hc, map_smul]
  rw [QQ_apply, Finset.smul_sum]
  simp_rw [key, hsc]
  rw [← map_sum, b.sum_repr]
end Formalism.InvariantFactorPaths.PW
