-- Prove2me | solution 1 for Formalism.FG.IntegralSubstitution.integral_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:45.252182+00:00
-- url     : https://prove2.me/submissions/6692fc0a-648c-46e0-a64a-08423186ef65

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.IntegralSubstitution
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.IntegralSubstitution
theorem _root_.solution : IntegralMv (1 : MvPowerSeries τ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
end Formalism.FG.IntegralSubstitution
