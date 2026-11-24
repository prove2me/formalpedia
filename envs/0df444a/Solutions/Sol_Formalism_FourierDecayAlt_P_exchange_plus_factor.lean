-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_plus_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:51.249821+00:00
-- url     : https://prove2.me/submissions/74f82478-c32c-495a-a9b3-6175fe1859b3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Xp_lift0_d0_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchangePlusFactor := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw
  exact Wd6.Xp_lift0_d0_comm σ w Y hσ hw.1
end Formalism.FourierDecayAlt.P
