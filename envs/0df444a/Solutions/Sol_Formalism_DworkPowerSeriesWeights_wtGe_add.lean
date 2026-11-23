-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:51.626796+00:00
-- url     : https://prove2.me/submissions/e4fd9b8d-8419-4a2b-a05d-a1092dc8fc87

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mono

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
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w1 w2 : ℝ}
    {f g : MvPowerSeries ι K} (hf : WtGe pi r w1 f) (hg : WtGe pi r w2 g) :
    WtGe pi r (min w1 w2) (f + g) := by
  intro n
  rw [monoWtGe_iff, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact wtGe_mono h0 h1 (min_le_left w1 w2) hf n
  · exact wtGe_mono h0 h1 (min_le_right w1 w2) hg n
end Formalism.DworkPowerSeriesWeights
