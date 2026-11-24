-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_fourth_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:11.269858+00:00
-- url     : https://prove2.me/submissions/2d065aa0-aef3-47b6-8253-beb09973a906

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch4

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchangePlusFactorTranspose := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw
  exact Wd6.exch4 σ w Y hσ hw.1
end Formalism.FourierDecayAlt.P
