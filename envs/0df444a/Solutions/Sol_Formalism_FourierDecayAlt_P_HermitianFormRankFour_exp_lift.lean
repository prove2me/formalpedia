-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.exp_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:12.200807+00:00
-- url     : https://prove2.me/submissions/929e293c-991d-43fe-9ec0-2237caeee883

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exp_semiconj
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]
variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution (hc : V * Vd + C * Cd = 1) (h1 : Vd * V = 1) (h2 : Vd * C = 0) (B : Matrix K K ℂ) :
    NormedSpace.exp (V * B * Vd) = V * NormedSpace.exp B * Vd + C * Cd := by
  have e1 : V * B * Vd * V = V * B := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : V * B * Vd * C = C * (0 : Matrix J J ℂ) := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero, Matrix.mul_zero]
  have s1 := exp_semiconj (V * B * Vd) B V e1
  have s2 := exp_semiconj (V * B * Vd) (0 : Matrix J J ℂ) C e2
  rw [NormedSpace.exp_zero, Matrix.mul_one] at s2
  calc NormedSpace.exp (V * B * Vd) = NormedSpace.exp (V * B * Vd) * (V * Vd + C * Cd) := by
        rw [hc, Matrix.mul_one]
    _ = V * NormedSpace.exp B * Vd + C * Cd := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, s1, s2]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
