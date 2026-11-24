-- Prove2me | solution 1 for Formalism.G.isCommOfRat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:09.006922+00:00
-- url     : https://prove2.me/submissions/3020a543-5d3f-461b-a01a-92a360d1631d

import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Theorems.Thm_Formalism_G_is_comm_of_rat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : IsCommOfRat := is_comm_of_rat
end Formalism.G
