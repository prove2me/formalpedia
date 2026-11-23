-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.hs_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:39.799798+00:00
-- url     : https://prove2.me/submissions/d0120e2e-45b2-4ef8-8738-c685f17e0370

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
theorem _root_.solution (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℝ) + 1) := by
  unfold hs
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.Sz3
