-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.norm_exp_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:43.666355+00:00
-- url     : https://prove2.me/submissions/4db5f90b-ff59-4e07-9683-b0af6eaeb2bd

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_norm_pow_mul_le

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
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution (x u : 𝔸) : ‖NormedSpace.exp x * u‖ ≤ Real.exp ‖x‖ * ‖u‖ := by
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • x ^ n) * u) (NormedSpace.exp x * u) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right u
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) * ‖u‖) (Real.exp ‖x‖ * ‖u‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_right ‖u‖
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [smul_mul_assoc, norm_smul, smul_eq_mul, mul_assoc, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_le x u n) (by positivity)
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp
