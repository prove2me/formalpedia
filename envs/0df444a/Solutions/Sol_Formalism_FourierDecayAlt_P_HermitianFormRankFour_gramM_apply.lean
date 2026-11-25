-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:54.36637+00:00
-- url     : https://prove2.me/submissions/c7d7c0bb-24bb-40b3-b96c-f40810e09fbb

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
theorem _root_.solution (H : Matrix N N ℂ) (U : J → N → ℂ) (W : K → N → ℂ) (i : J) (j : K) :
    ((colM U)ᴴ * H * colM W) i j = herm H (W j) (U i) := by
  simp only [herm, colM, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
