-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.v_one_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:58.300353+00:00
-- url     : https://prove2.me/submissions/9185e4f9-ff64-4d55-a080-bd4980cb666f

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
theorem _root_.solution (c : Cfg) (hc : c.Ok) : 0 ≤ c.v 1 := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have h1 := hc.hDel
  have h2 := hc.hv0
  unfold Cfg.v
  push_cast
  nlinarith
end Formalism.FourierDecayAlt.P.Sz4
