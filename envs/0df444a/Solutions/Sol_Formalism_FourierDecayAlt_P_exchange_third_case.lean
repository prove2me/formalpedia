-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_third_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:40.991689+00:00
-- url     : https://prove2.me/submissions/63c324b1-4041-44a6-9459-52691612039c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch3

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorTranspose := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw hY
  exact Wd6.exch3 σ w Y hσ hw.1 hw.2.1 hY
end Formalism.FourierDecayAlt.P
