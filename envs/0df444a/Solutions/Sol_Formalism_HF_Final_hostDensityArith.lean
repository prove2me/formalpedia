-- Prove2me | solution 1 for Formalism.HF.Final.hostDensityArith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:23.305745+00:00
-- url     : https://prove2.me/submissions/ebc22a85-513a-4861-a554-8af910c53b2f

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_Final_apLogDensity
import Theorems.Thm_Formalism_HF_Final_logToDir
import Theorems.Thm_Formalism_HF_apLogDensity
import Theorems.Thm_Formalism_HF_hostDensityArith_of
import Theorems.Thm_Formalism_HF_logToDir


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
theorem _root_.solution : Formalism.HF.HostDensityArith := Formalism.HF.hostDensityArith_of apLogDensity logToDir
end Formalism.HF.Final
