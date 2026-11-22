-- Prove2me | solution 1 for Formalism.FG.IntegralSubstitution.integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:45.011911+00:00
-- url     : https://prove2.me/submissions/159d4063-22e3-45b5-b543-e9b49dea06fb

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
theorem _root_.solution {A B : MvPowerSeries τ K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) (hB _)
end Formalism.FG.IntegralSubstitution
