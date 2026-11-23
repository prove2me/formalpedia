-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.cap_values_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:20.658091+00:00
-- url     : https://prove2.me/submissions/dd0a5c63-9223-4b0a-bbcb-049300d1d1b4

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound

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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d)
    (I : Set ℕ) : BddAbove ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) '' I) := by
  apply Set.Finite.bddAbove
  apply (Set.finite_range (fun t : ZMod d => capL d TT nu1 nu2 t)).subset
  rintro _ ⟨i, _, rfl⟩
  exact ⟨_, rfl⟩
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
