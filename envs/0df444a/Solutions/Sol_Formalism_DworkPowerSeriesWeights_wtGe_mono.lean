-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:18.202956+00:00
-- url     : https://prove2.me/submissions/61c3e547-bb4a-4644-8fcb-689dc6b54222

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w w' : ℝ} (hw : w' ≤ w)
    {f : MvPowerSeries ι K} (hf : WtGe pi r w f) : WtGe pi r w' f := fun n =>
  le_trans (monoWtGe_iff.mp (hf n)) (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))
end Formalism.DworkPowerSeriesWeights
