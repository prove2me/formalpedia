-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.v_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:40.044976+00:00
-- url     : https://prove2.me/submissions/e1b0fb36-71c6-4721-9357-b18af93b04a5

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_sub

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
theorem _root_.solution (c : Cfg) (hc : c.Ok) (i j : ℕ) (hij : i < j) : c.v j < c.v i := by
  have h := v_sub c i j
  have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have h2 := hc.hDel
  nlinarith
end Formalism.FourierDecayAlt.P.Sz4
