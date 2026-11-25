-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:37.374082+00:00
-- url     : https://prove2.me/submissions/3908c7c7-6b4c-418a-af4d-6efa41bd6123

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exists_skew_hermitian_log_unitary

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
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := exists_skew_hermitian_log_unitary A hA
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
