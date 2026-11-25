-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:06:55.139728+00:00
-- url     : https://prove2.me/submissions/973fb852-dfe6-461e-83d6-e0025fed5545

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) (dOp π X) 0 := by
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hc.comp_continuous h1 (exp_uw hX)
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)))
    (by simp [NormedSpace.exp_zero, hπ.1])
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.2 _ (exp_uw hX s) _ (exp_uw hX t)]) hcont
  exact (hA 0).differentiableAt.hasDerivAt
end Formalism.FourierDecayAlt.P.QrD
