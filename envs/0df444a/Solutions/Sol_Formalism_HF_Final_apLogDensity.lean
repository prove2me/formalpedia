-- Prove2me | solution 1 for Formalism.HF.Final.apLogDensity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:21.425035+00:00
-- url     : https://prove2.me/submissions/44f6bdb6-d964-4bb4-a866-79705f4ea776

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_apLogDensity


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
theorem _root_.solution : Formalism.HF.APLogDensity := Formalism.HF.apLogDensity
end Formalism.HF.Final
