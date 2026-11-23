-- Prove2me | solution 1 for Formalism.HF.Final.quadDiscr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:13.467599+00:00
-- url     : https://prove2.me/submissions/6badf15f-ea3a-48fe-9be2-8fd7b2180fc8

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_quadDiscr


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
theorem _root_.solution : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
end Formalism.HF.Final
