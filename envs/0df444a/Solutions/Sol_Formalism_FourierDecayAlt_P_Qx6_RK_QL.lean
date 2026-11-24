-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RK_QL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:57:40.780838+00:00
-- url     : https://prove2.me/submissions/c691a5d5-f82a-4260-a38b-bfcf16b01d48

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_dom_Dcell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_ind_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_Res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sdata_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_om_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_stepOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_step_fam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
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
theorem _root_.solution (hCS : ChainStep) (hR : ResMem) (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hW : WeylLevelElementFacts)
    (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l : Fin r) (Y : ℂ)
    (a b : Fin 2) : Pres2 (RK z z' π π' D l) (QL k r z z' l.castSucc Y a b) (stepOp z z' l Y a b) := by
  intro Φ Ψ h
  have hRes : FamFF k r z z' π π' l.succ (Dcell D l.succ) (Res k r l Φ) := by
    rw [Dcell_succ]
    exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) h.1
  have h2 := RS_stepOp (π := π) (π' := π') hFO hTP hLL hz hz' l (sdata_self hR hz hz' hD l.succ) (om_stable l) Y a b
    Ψ (Res k r l Φ) ⟨h.2.2.1, hRes, h.2.2.2⟩
  refine ⟨fam_QL hTP hz hz' (dom_Dcell hR hz hz' hD _) Y a b h.1, ind_QL z z' _ Y a b h.2.1, h2.1, ?_⟩
  intro c hc g hg hgD
  rw [h2.2.2 c hc g hg hgD]
  exact step_fam hCS hR hFO hTP hLL hW hz hz' hD l Y a b h.1 h.2.1 hc hg hgD
end Formalism.FourierDecayAlt.P.Qx6
