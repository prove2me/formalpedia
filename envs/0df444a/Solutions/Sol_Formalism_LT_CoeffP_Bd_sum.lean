-- Prove2me | solution 1 for Formalism.LT.CoeffP.Bd.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:17.957356+00:00
-- url     : https://prove2.me/submissions/3fbec275-2857-4776-9d14-23dbc6e6c24f

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne

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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
namespace Bd
theorem _root_.solution {α : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset α} {F : α → MvPowerSeries ι K}
    (h : ∀ i ∈ s, Bd a (F i)) : Bd a (∑ i ∈ s, F i) := by
  intro d
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha (fun i hi => h i hi d)
end Bd
end Formalism.LT.CoeffP
