-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.representation_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:49.919931+00:00
-- url     : https://prove2.me/submissions/e0d61dd8-aa9f-4a41-b70d-40fee7b15f89

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_group_eq_exp
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_dOp_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_exp_uw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_lcurve_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_one_parameter_differentiable
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f


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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.PiExp := by
  intro W _ _ _ k r z π hπ X hX t
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hπ.2.comp_continuous h1 (QrD.exp_uw hX)
  have h0 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0 = 1 := by
    simp [NormedSpace.exp_zero, hπ.1.1]
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) h0
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.1.2 _ (QrD.exp_uw hX s) _ (QrD.exp_uw hX t)]) hcont
  have hAd : QrD.dOp π X = A := by
    have h := (QrD.dOp_hasDeriv hπ.1 hπ.2 hX).unique (hA 0)
    have h0' : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := h0
    rw [h, h0']
    exact ContinuousLinearMap.id_comp A
  have h := GroupGeneratedByExp.group_eq_exp _ A h0 hA t
  rw [hAd]
  exact h
end Formalism.FourierDecayAlt.P
