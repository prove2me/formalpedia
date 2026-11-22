-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:27.029058+00:00
-- url     : https://prove2.me/submissions/5443161a-553f-4fa0-9c8d-5d375cc029c6

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
theorem _root_.solution {pi : ℝ} {r : ι → ℝ} {wt wt' : ℝ} (h : wt = wt') {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) : WtGe pi r wt' f := by
  subst h
  exact hf
end Formalism.DworkPowerSeriesWeights
