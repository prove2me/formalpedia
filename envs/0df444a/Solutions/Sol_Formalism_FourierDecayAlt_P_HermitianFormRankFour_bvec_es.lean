-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.bvec_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:53.498915+00:00
-- url     : https://prove2.me/submissions/ba9acdf7-d8a5-4094-9ac2-5678ca589c66

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution (c c' : Fin r) : bvec (eI k r c') (esI k r c) = 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
