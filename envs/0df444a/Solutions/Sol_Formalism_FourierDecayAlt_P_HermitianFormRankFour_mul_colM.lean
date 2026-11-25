-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.mul_colM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:24.229061+00:00
-- url     : https://prove2.me/submissions/55f57cb0-1495-49be-b4e1-cf4583dacec1

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
theorem _root_.solution (h : Matrix N N ℂ) (U : J → N → ℂ) : h * colM U = colM fun j => h *ᵥ U j := rfl
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
