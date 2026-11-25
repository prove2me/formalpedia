-- Prove2me | solution 1 for Formalism.HN.size_maximal_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:41.968607+00:00
-- url     : https://prove2.me/submissions/879151a8-bf2b-4da3-8333-ae61cd9095cf

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Theorems.Thm_Formalism_HN_sizeMu_of
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : SizeMu := by
  exact sizeMu_of place_lattice_structure
end Formalism.HN
