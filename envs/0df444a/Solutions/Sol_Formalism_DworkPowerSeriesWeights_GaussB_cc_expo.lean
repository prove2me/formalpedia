-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.GaussB.cc_expo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:06:16.366796+00:00
-- url     : https://prove2.me/submissions/a64b355f-63dc-4df4-919d-441cd63ee33b

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
theorem _root_.solution {K : Type} [Field K] {H : Type} [Fintype H] {N0 N1 : ℕ} (S : K) (u : H → K) :
    MvPowerSeries.constantCoeff ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
      MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) :
        MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero, mul_zero]
  intro t _
  rw [map_sum]
  refine Finset.sum_eq_zero fun ab _ => ?_
  simp
end Formalism.DworkPowerSeriesWeights.GaussB
