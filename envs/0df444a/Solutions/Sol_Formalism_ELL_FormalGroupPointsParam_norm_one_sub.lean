-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.norm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:35.695707+00:00
-- url     : https://prove2.me/submissions/94b61fce-e49c-4448-a62e-62949461b7eb

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_neq

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
theorem _root_.solution {E : K} (hE : ‖E‖ < 1) : ‖1 - E‖ = 1 := by
  rw [sub_eq_add_neg, neq (by rw [norm_neg, norm_one]; exact hE), norm_one]
end Formalism.ELL.FormalGroupPointsParam
