-- Prove2me | solution 1 for Formalism.HF.Final.hostDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:52.249374+00:00
-- url     : https://prove2.me/submissions/90c49b51-78e7-417f-897c-54d1754f6c5c

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_Final_hostDensityArith
import Theorems.Thm_Formalism_HF_hostDensity_of


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
theorem _root_.solution : Formalism.HF.HostDensity := Formalism.HF.hostDensity_of hostDensityArith
end Formalism.HF.Final
