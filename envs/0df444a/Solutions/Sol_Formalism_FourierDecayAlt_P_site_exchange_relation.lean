-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.site_exchange_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:22.524889+00:00
-- url     : https://prove2.me/submissions/7f1627fa-35bf-4341-a8df-e1a02560b357

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_wd_siteStep_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_fourth_case
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_plus_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_second_case
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_third_case


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.SiteStep :=
  wd_siteStep_of exchange_plus_factor exchange_second_case exchange_third_case exchange_fourth_case
end Formalism.FourierDecayAlt.P
