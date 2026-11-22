-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:20.173058+00:00
-- url     : https://prove2.me/submissions/a92d0f56-719b-408b-a61c-9020cccf6a05

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r wt (F i)) :
    WtGe pi r wt (∑ i ∈ s, F i) := by
  intro n
  rw [monoWtGe_iff, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun i hi => h i hi n
end Formalism.DworkPowerSeriesWeights
