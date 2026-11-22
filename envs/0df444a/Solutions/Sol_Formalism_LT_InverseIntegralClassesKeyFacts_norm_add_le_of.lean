-- Prove2me | solution 1 for Formalism.LT.InverseIntegralClassesKeyFacts.norm_add_le_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:15.714587+00:00
-- url     : https://prove2.me/submissions/28c20f1d-56eb-469f-a36e-8d8683f5d1b1

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT
open Formalism.G
open Formalism.LT.InverseIntegralClassesKeyFacts
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.InverseIntegralClassesKeyFacts
theorem _root_.solution {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
end Formalism.LT.InverseIntegralClassesKeyFacts
