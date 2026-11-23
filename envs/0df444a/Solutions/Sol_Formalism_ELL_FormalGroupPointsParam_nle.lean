-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.nle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:15.999632+00:00
-- url     : https://prove2.me/submissions/b5bb54e3-6fa5-466e-aa84-58f6ceea2d14

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef

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
theorem _root_.solution {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
end Formalism.ELL.FormalGroupPointsParam
