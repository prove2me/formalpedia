-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.smp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:57.557+00:00
-- url     : https://prove2.me/submissions/34e50fb4-49f2-4803-bdb2-78b49a562575

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact smm hb.le ha
end Formalism.ELL.FormalGroupPointsParam
