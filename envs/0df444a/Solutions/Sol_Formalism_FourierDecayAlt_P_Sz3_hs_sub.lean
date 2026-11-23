-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.hs_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:38.757798+00:00
-- url     : https://prove2.me/submissions/22dbbfa0-b1b4-46ff-a913-8dd3690352fe

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (p J : ℕ) (h : p ≤ J) : ∑ d ∈ Ioc p J, 1 / (d : ℝ) = hs J - hs p := by
  unfold hs
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) h]
  ring
end Formalism.FourierDecayAlt.P.Sz3
