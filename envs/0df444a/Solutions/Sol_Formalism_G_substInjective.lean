-- Prove2me | solution 1 for Formalism.G.substInjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:02.21201+00:00
-- url     : https://prove2.me/submissions/3341eeca-c67b-4e04-bcde-8f67ae7d5e54

import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Theorems.Thm_Formalism_G_substInjective_statement


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
theorem _root_.solution : SubstInjective := substInjective_statement
end Formalism.G
