-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.sum_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:38.771907+00:00
-- url     : https://prove2.me/submissions/f5473ca0-c044-41a3-a5ea-b5c6b32244a6

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
theorem _root_.solution (n : ℕ) : ∑ d ∈ Icc 1 n, 1 / (d : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two
end Formalism.FourierDecayAlt.P.Sz3
