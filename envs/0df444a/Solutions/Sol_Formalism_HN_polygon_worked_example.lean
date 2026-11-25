-- Prove2me | solution 1 for Formalism.HN.polygon_worked_example
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:07.086607+00:00
-- url     : https://prove2.me/submissions/86c1cc43-a8b9-40e6-85f8-a2455d90ffaa

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_example_of
import Theorems.Thm_Formalism_HN_degree_supermodular
import Theorems.Thm_Formalism_HN_finite_supremum_slopes
import Theorems.Thm_Formalism_HN_hnStep_of
import Theorems.Thm_Formalism_HN_maximal_slope_ratio
import Theorems.Thm_Formalism_HN_polygon_slopes_characterization
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
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution : Example := example_of slope_characterization
  (hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties)
  polygon_slopes_characterization
end Formalism.HN
