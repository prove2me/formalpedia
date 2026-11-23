-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnxRes_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:59.701611+00:00
-- url     : https://prove2.me/submissions/03409168-a5ca-4689-ad03-2e814f1ea5f9

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (m : V2 d →₀ ℕ) (s : ZMod d) (z : V2 d) :
    bnxRes m s z = if z.2 = s then m z else 0 := by
  obtain ⟨b, t⟩ := z
  by_cases h : t = s
  · subst h
    cases b <;> simp [bnxRes, Finsupp.single_apply]
  · cases b <;> simp [bnxRes, Finsupp.single_apply, h, Ne.symm h]
end Formalism.DworkPowerSeriesWeights
