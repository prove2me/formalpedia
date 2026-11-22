-- Prove2me | solution 1 for Formalism.LT.InverseIntegralClassesKeyFacts.norm_sub_le_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:58.688968+00:00
-- url     : https://prove2.me/submissions/a6d7c829-667a-4e50-a3d5-d43c74f58cb7

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_add_le_of

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
theorem _root_.solution {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)
end Formalism.LT.InverseIntegralClassesKeyFacts
