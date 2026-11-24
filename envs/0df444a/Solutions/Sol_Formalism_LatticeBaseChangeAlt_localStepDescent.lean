-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localStepDescent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:55.794139+00:00
-- url     : https://prove2.me/submissions/2726a338-ea56-43d8-a769-f0ec63324ffb

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSmulMemOfMemSpan
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_finrank_span_image_alt
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_index_baseChange_lattice
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_inter_baseChange_lattice
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepDescent_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LocalStepDescent :=
  localStepDescent_of finrank_span_image_alt inter_baseChange_lattice index_baseChange_lattice
end Formalism.LatticeBaseChangeAlt
