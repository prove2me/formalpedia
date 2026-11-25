-- Prove2me | solution 1 for Formalism.HN.slope_characterization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:01.172171+00:00
-- url     : https://prove2.me/submissions/d5866057-1712-438f-8e85-7f9291f88cf4

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Theorems.Thm_Formalism_HN_muChar_of
import Theorems.Thm_Formalism_HN_maximal_slope_ratio
import Theorems.Thm_Formalism_HN_real_saturation_property
import Theorems.Thm_Formalism_HN_saturation_basic_properties


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
universe u v w
namespace Formalism.HN
theorem _root_.solution : MuChar := muChar_of real_saturation_property saturation_basic_properties maximal_slope_ratio
end Formalism.HN
