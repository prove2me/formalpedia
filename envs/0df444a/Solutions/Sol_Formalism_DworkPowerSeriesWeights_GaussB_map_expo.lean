-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.GaussB.map_expo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:26.995524+00:00
-- url     : https://prove2.me/submissions/222b96ec-873f-4da7-a079-71538e1cfc0b

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
theorem _root_.solution {F K : Type} [Field F] [Field K] (φ : F →+* K) {H : Type} [Fintype H] {N0 N1 : ℕ}
    (S : F) (u : H → F) :
    MvPowerSeries.map φ ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
      MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) :
        MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) F) =
      (-(φ S)) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (φ (u t)) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, ← MvPowerSeries.smul_eq_C_mul,
    map_neg]
  simp only [map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]
end Formalism.DworkPowerSeriesWeights.GaussB
