-- Prove2me | solution 1 for Formalism.HF.Final.mqDiscr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:56:27.555803+00:00
-- url     : https://prove2.me/submissions/111954bd-8a42-4580-8065-c5b0254ab247

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_HF_Final_quadDiscr
import Theorems.Thm_Formalism_HF_mqDiscr_of
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
theorem _root_.solution : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr
end Formalism.HF.Final
