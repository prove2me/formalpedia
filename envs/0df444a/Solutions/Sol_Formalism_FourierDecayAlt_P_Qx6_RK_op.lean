-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RK_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:51.837827+00:00
-- url     : https://prove2.me/submissions/88820ed4-fc5e-4533-8e0b-74c67a93e58c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_Dcell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_mul_mem_of_mem_inv_mul_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_dom_Dcell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_dir
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_germ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_near_pt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_ind_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_Res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution (hR : ResMem) (hFO : FamOps) (hW : WeylLevelElementFacts) (hz : inWb k r z) (hz' : inWb k r z')
    {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l j : Fin r) (hj : j.val < l.val) (q : Fin 6) :
    Pres2 (RK z z' π π' D l) (crd (opL j q)) (crd (opL j q)) := by
  intro Φ Ψ h
  refine ⟨hFO Wp Wq k r z z' π π' _ _ Φ hz hz' (open_Dcell hD.1 _) h.1 j q, ind_op j hj q h.2.1,
    hFO Wp Wq k r z z' π π' _ _ Ψ hz hz' (open_Dcell hD.1 _) h.2.2.1 j q, ?_⟩
  intro c hc g hg hgD
  have hne : l ≠ j := fun e => by rw [e] at hj; exact lt_irrefl _ hj
  have e1 : opL j q (fun c' => Ψ c' g) c = opL j q (fun c' => Res k r l Φ c' g) c := by
    apply opL_germ
    filter_upwards [near_pt (open_Dcell hD.1 l.succ) hc hgD] with c' hc'
    exact h.2.2.2 c' hc'.1 g hg hc'.2
  have hRes : FamFF k r z z' π π' l.succ (Dcell D l.succ) (Res k r l Φ) := by
    rw [Dcell_succ]
    exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) h.1
  have hgD' : w1 k r l (c l) * g ∈ Dcell D l.castSucc c := by
    rw [Dcell_succ] at hgD
    exact hgD
  have e2 := opL_dir j q (f₁ := fun c' => Res k r l Φ c' g) (f₂ := fun c' => Φ c' (w1 k r l (c l) * g)) (c := c)
    ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) (fam_diff hRes hc hg hgD)
    (fam_diff h.1 hc (mul_mem_of_mem_inv_mul_ideal hW l (hc l) hg) hgD')
    (Filter.Eventually.of_forall fun s => by
      show _ • Φ _ _ = _
      rw [Function.update_of_ne hne])
  exact e1.trans e2
end Formalism.FourierDecayAlt.P.Qx6
