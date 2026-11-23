-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_intCast_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:39.818048+00:00
-- url     : https://prove2.me/submissions/4de569d1-0298-4bd8-92cb-f5d30b8b605d

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) [Fact l.Prime] (z : ℤ) :
    ‖(z : ℂ_[l])‖ = ‖(z : ℚ_[l])‖ := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']
end Formalism.DworkPowerSeriesWeights
