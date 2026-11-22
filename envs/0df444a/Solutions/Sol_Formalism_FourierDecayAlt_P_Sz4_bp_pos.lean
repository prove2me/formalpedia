-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.bp_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:34.440424+00:00
-- url     : https://prove2.me/submissions/0b243b19-8b67-4621-9cdb-228435db058b

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
theorem _root_.solution (c : Cfg) (hc : c.Ok) (ht : c.top = true) : 0 < c.bp := by
  have := (hc.htop ht).1
  linarith [hc.hb1]
end Formalism.FourierDecayAlt.P.Sz4
