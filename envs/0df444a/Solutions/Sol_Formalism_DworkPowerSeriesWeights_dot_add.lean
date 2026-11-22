-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dot_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:16.011131+00:00
-- url     : https://prove2.me/submissions/579e46a2-a434-4331-84ca-4df043e9d894

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound

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
theorem _root_.solution (m n : ι →₀ ℕ) (r : ι → ℝ) : dot (m + n) r = dot m r + dot n r := by
  classical
  unfold dot
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)
end Formalism.DworkPowerSeriesWeights
