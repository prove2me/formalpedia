-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.exp_semiconj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:53:49.761995+00:00
-- url     : https://prove2.me/submissions/3e8c42f7-3316-4f10-a07d-ba061efb2fb5

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution (X : Matrix N N ℂ) (B : Matrix K K ℂ) (V : Matrix N K ℂ) (h : X * V = V * B) :
    NormedSpace.exp X * V = V * NormedSpace.exp B := by
  letI : NormedRing (Matrix N N ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix N N ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix K K ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix K K ℂ) := Matrix.linftyOpNormedAlgebra
  have hp : ∀ n : ℕ, X ^ n * V = V * B ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  let fL : Matrix N N ℂ →+ Matrix N K ℂ := ⟨⟨fun M => M * V, Matrix.zero_mul V⟩, fun a b => Matrix.add_mul a b V⟩
  let fR : Matrix K K ℂ →+ Matrix N K ℂ := ⟨⟨fun M => V * M, Matrix.mul_zero V⟩, fun a b => Matrix.mul_add V a b⟩
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).map fL
    (show Continuous (fun M : Matrix N N ℂ => M * V) from continuous_id.matrix_mul continuous_const)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).map fR
    (show Continuous (fun M : Matrix K K ℂ => V * M) from continuous_const.matrix_mul continuous_id)
  have e : (⇑fL ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) = (⇑fR ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) := by
    funext n
    simp only [Function.comp_apply, fL, fR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul, hp]
  rw [e] at h1
  exact h1.unique h2
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
