-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.GaussB.jetsIntegral_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:06:18.132802+00:00
-- url     : https://prove2.me/submissions/bb07d8f3-7ded-4ff0-a939-d7d0d6d89594

import Definitions.Def_Formalism_GaussJetBounds_StatementY
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.GaussB
namespace Formalism.DworkPowerSeriesWeights.GaussB
theorem _root_.solution {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K)
    (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {sg : MvPowerSeries ι F} (h : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.map φ sg) := by
  intro κ
  rw [MvPowerSeries.coeff_map, ← map_natCast φ, ← map_mul, hφ]
  exact h κ
end Formalism.DworkPowerSeriesWeights.GaussB
