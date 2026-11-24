-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.chainAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:08.841895+00:00
-- url     : https://prove2.me/submissions/95026427-7603-451a-8044-c39df5a229f0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_wCell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_resG_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_resG_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_mul_mem_of_mem_inv_mul_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_sandwich
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_ind_resG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RK_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RK_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RK_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hCS : ChainStep) (hR : ResMem) (hRG : ResGFam) (hFO : FamOps) (hTP : TPreservesFF)
    (hLL : TLinLoc) (hW : WeylLevelElementFacts) : ChainAll := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y a b hz hz' hD J hJ
  induction i using Fin.induction generalizing a b with
  | zero =>
    intro c _ g _ _
    have e : resG k r 0 J c = J := funext fun x => resG_zero J c x
    show resG k r 0 _ c g = tL k r z z' 0 Y a b (resG k r 0 J c) g
    rw [resG_zero, e]
  | succ l ih =>
    intro c hc g hg hgD
    have h0 : RK z z' π π' D l (resG k r l.castSucc J) (resG k r l.succ J) :=
      ⟨hRG Wp Wq k r z z' π π' D hz hz' hD J hJ _, ind_resG l.castSucc J, hRG Wp Wq k r z z' π π' D hz hz' hD J hJ _,
        fun c _ g _ _ => by rw [resG_succ]⟩
    have h1 := preserves_sandwich (R := RK z z' π π' D l) (RK_lin D l) Y l.val
      (fun j hj q => RK_op hR hFO hW hz hz' hD l j hj q)
      (M := QL k r z z' l.castSucc Y) (M' := stepOp z z' l Y)
      (fun a b => RK_QL hCS hR hFO hTP hLL hW hz hz' hD l Y a b) a b _ _ h0
    have h2 := h1.2.2.2 c hc g hg hgD
    have e : sandw k r Y l.succ.val (QL k r z z' l.succ Y) =
        sandw k r Y l.val (stepOp (Wp := Wp) (Wq := Wq) z z' l Y) := by
      show sandw k r Y (l.val + 1) _ = _
      show sandw k r Y l.val _ = _
      rw [dif_pos l.isLt]
      rfl
    rw [e, h2, resG_succ]
    show _ • _ = _ • _
    congr 1
    have hgD' : wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D := by
      have : wCell k r l.succ c * g ∈ D := hgD
      rwa [wCell_succ, Matrix.mul_assoc] at this
    exact ih a b c hc _ (mul_mem_of_mem_inv_mul_ideal hW l (hc l) hg) hgD'
end Formalism.FourierDecayAlt.P.Qx6
