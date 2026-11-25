-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.bvec_ss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:49.700334+00:00
-- url     : https://prove2.me/submissions/bec2d2b1-63cc-4a37-8f2f-43ec7be7f04b

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
theorem _root_.solution (c c' : Fin r) : bvec (esI k r c') (esI k r c) = if c = c' then 1 else 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
