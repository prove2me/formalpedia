-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:23.918803+00:00
-- url     : https://prove2.me/submissions/62e2c620-4154-4fc5-9eb4-0f8094f56c25

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight

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
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (wt : ℝ) :
    WtGe pi r wt (0 : MvPowerSeries ι K) := by
  intro n
  unfold MonoWtGe
  rw [map_zero, norm_zero]
  exact Real.rpow_nonneg h0.le _
end Formalism.DworkPowerSeriesWeights
