-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.rd_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:12.512073+00:00
-- url     : https://prove2.me/submissions/d8fbb0df-92e7-4edc-b5ea-8124f952d377

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_exp_uw
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_dOp_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_mem_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_J_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : RdV X F g = (J g).comp ((dOp π' X).comp B) := by
  have hfun : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_right hD hg hu), J_right hπ' hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold RdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp) (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B))
      ((J g).comp ((dOp π' X).comp B)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv
end Formalism.FourierDecayAlt.P.QrD
