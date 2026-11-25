-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.group_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:22.087045+00:00
-- url     : https://prove2.me/submissions/20e069e1-2e03-4907-8c38-e2e5d31c7375

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution (φ : ℝ → (W →L[ℂ] W)) (A : W →L[ℂ] W) (h0 : φ 0 = 1)
    (hA : ∀ t, HasDerivAt φ ((φ t).comp A) t) (t : ℝ) : φ t = NormedSpace.exp (t • A) := by
  have hcW : CompleteSpace W := FiniteDimensional.complete ℂ W
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := NormedAlgebra.restrictScalars ℚ ℂ (W →L[ℂ] W)
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-A)))
      ((-A) * NormedSpace.exp (s • (-A))) s := fun s => hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s
  have hψ : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ u * NormedSpace.exp (u • (-A))) 0 s := by
    intro s
    have h := (hA s).mul (hE s)
    have e : (φ s).comp A * NormedSpace.exp (s • (-A)) + φ s * ((-A) * NormedSpace.exp (s • (-A))) = 0 := by
      show φ s * A * _ + _ = 0
      noncomm_ring
    rwa [e] at h
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hconst
  have hinv : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    exact (((Commute.refl A).neg_left).smul_left _).smul_right _
  calc φ t = φ t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp
