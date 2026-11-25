-- Prove2me | solution 1 for Formalism.HN.slope_inequality_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:55.570613+00:00
-- url     : https://prove2.me/submissions/94f41619-a6e2-44c7-975e-ac69ee942ed9

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Theorems.Thm_Formalism_HN_slopeIneq_of
import Theorems.Thm_Formalism_HN_real_saturation_property
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_slope_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe uR uV uW uE uF
namespace Formalism.HN
theorem _root_.solution : SlopeIneq := slopeIneq_of slope_characterization slope_characterization real_saturation_property saturation_basic_properties saturation_basic_properties
end Formalism.HN
