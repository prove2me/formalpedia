-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:55.293844+00:00
-- url     : https://prove2.me/submissions/2977aa29-3d4f-4942-880c-bbd49e19dbf4

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
theorem _root_.solution (e : N ≃ K ⊕ J) (h1 : Vd * V = 1) (h2 : Vd * C = 0) (h3 : Cd * V = 0) (h4 : Cd * C = 1) :
    V * Vd + C * Cd = 1 := by
  have hQP : fromRows Vd Cd * fromCols V C = 1 := by
    rw [fromRows_mul_fromCols, h1, h2, h3, h4, fromBlocks_one]
  have := (mul_eq_one_comm_of_equiv e).mpr hQP
  rwa [fromCols_mul_fromRows] at this
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
