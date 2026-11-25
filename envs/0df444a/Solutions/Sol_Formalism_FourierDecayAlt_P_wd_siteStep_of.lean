-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.wd_siteStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:56.480427+00:00
-- url     : https://prove2.me/submissions/9fb28d8b-f462-4b5d-816f-30dc69d0b908

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_site_step_of

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
theorem _root_.solution (hE1 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactor) (hE2 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorStar)
    (hE3 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorTranspose) (hE4 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactorTranspose) : Formalism.FourierDecayAlt.Wd.SiteStep := by
  intro K A S _ _ _ _ _ _ _ _ σ QQ QQ' w hσ hQ hrec hw
  exact Wd7.site_step_of hE1 hE2 hE3 hE4 σ QQ QQ' w hσ hQ hrec hw
end Formalism.FourierDecayAlt.P
