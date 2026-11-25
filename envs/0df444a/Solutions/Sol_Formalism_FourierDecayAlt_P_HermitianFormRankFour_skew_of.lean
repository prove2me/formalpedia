-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.skew_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:56.509559+00:00
-- url     : https://prove2.me/submissions/f181ab3b-6feb-43a3-8e6f-759079318dc3

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
theorem _root_.solution {H : Matrix N N ℂ} (hH : Hᴴ = H) {B : Matrix K K ℂ} (hB : Bᴴ = -B) :
    (V * B * (Vᴴ * H))ᴴ * H + H * (V * B * (Vᴴ * H)) = 0 := by
  simp [conjTranspose_mul, hH, hB, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
