-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.bvec_se
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:10.147422+00:00
-- url     : https://prove2.me/submissions/e5dddd63-b070-4f2f-b90c-902bed663dee

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
theorem _root_.solution (c c' : Fin r) : bvec (esI k r c') (eI k r c) = 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
