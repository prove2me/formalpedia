-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_vanishing_differential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:08.638842+00:00
-- url     : https://prove2.me/submissions/e19adb98-7247-4231-bb9b-383980107bd9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FibreExpansionZeroFails
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingDifferential
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_big_cell_vanishing_of_commute__266cd2982839


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
theorem _root_.solution (hJ : C6.JCommuteBig) : C6.BigCellVanishing :=
  big_cell_vanishing_of_commute' hJ
end Formalism.FourierDecayAlt.P
