-- Prove2me | solution 1 for Formalism.HF.Final.hostDiscr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:51.251452+00:00
-- url     : https://prove2.me/submissions/12ce6c81-6088-4ce1-94ce-921447a5f5f7

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_Final_mqDiscr
import Theorems.Thm_Formalism_HF_hostDiscr_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HF Formalism.HF.Final
namespace Formalism.HF.Final
theorem _root_.solution : Formalism.HF.HostDiscr := Formalism.HF.hostDiscr_of mqDiscr
end Formalism.HF.Final
