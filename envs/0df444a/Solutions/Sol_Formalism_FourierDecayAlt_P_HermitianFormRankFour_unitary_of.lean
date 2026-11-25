-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:51:36.403+00:00
-- url     : https://prove2.me/submissions/9d820b74-7b18-4abb-be72-f078e58b54dc

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
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
theorem _root_.solution {H h : Matrix N N ℂ} (hH : Hᴴ = H) (hh : hᴴ * H * h = H) (h1 : Vᴴ * H * V = 1)
    (e1 : h * V = V * (Vᴴ * H * h * V)) : (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * h * V) = 1 := by
  have k1 : (h * V)ᴴ * H * (h * V) = 1 := by
    rw [conjTranspose_mul, show Vᴴ * hᴴ * H * (h * V) = Vᴴ * (hᴴ * H * h) * V by simp only [Matrix.mul_assoc],
      hh, h1]
  rw [e1, conjTranspose_mul,
    show (Vᴴ * H * h * V)ᴴ * Vᴴ * H * (V * (Vᴴ * H * h * V)) =
      (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * V) * (Vᴴ * H * h * V) by simp only [Matrix.mul_assoc],
    h1, Matrix.mul_one] at k1
  exact k1
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
