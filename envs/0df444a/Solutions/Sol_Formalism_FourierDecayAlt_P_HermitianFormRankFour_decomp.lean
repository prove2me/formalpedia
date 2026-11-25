-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:44:39.016869+00:00
-- url     : https://prove2.me/submissions/7ac3daac-fa24-4fed-95e0-f2d656cb34cd

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour

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
theorem _root_.solution (hc : V * Vd + C * Cd = 1) (h3 : Cd * V = 0) (h : Matrix N N ℂ) (hC : h * C = C) (hCd : Cd * h = Cd) :
    h * V = V * (Vd * h * V) ∧ h = V * (Vd * h * V) * Vd + C * Cd := by
  have e1 : h * V = V * (Vd * h * V) := by
    calc h * V = (V * Vd + C * Cd) * (h * V) := by rw [hc, Matrix.one_mul]
      _ = V * (Vd * h * V) + C * (Cd * h * V) := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = V * (Vd * h * V) := by rw [hCd, h3, Matrix.mul_zero, add_zero]
  refine ⟨e1, ?_⟩
  calc h = h * (V * Vd + C * Cd) := by rw [hc, Matrix.mul_one]
    _ = h * V * Vd + h * C * Cd := by simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = V * (Vd * h * V) * Vd + C * Cd := by rw [e1, hC]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
