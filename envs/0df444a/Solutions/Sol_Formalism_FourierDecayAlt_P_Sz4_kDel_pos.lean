-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.kDel_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:48.25229+00:00
-- url     : https://prove2.me/submissions/3e873cf0-0a8a-4158-933d-11cdfce2d455

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (hc : c.Ok) : 0 < 4 * (c.k : ℝ) * c.Del := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  positivity
end Formalism.FourierDecayAlt.P.Sz4
