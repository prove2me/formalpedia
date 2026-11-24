-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.final_massBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:41.156123+00:00
-- url     : https://prove2.me/submissions/0acbc08d-b290-4c89-9e08-ed25147eb88c

import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : MassBasic := Formalism.HermitianLatticesTheory.massBasic
end Formalism.HermitianLatticesTheory
