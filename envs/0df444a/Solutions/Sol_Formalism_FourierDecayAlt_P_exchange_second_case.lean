-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_second_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:45.57605+00:00
-- url     : https://prove2.me/submissions/43291b24-87e4-4706-bc90-db271b537e1e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch2

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorStar := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw hY
  exact Wd6.exch2 σ w Y hσ hw.1 hw.2.1 hY
end Formalism.FourierDecayAlt.P
