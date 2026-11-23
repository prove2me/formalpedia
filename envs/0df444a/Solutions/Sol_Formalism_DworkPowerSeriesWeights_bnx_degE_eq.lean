-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_degE_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:00.496145+00:00
-- url     : https://prove2.me/submissions/9eb3702d-44cf-43f8-98d6-94748a9c2e92

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0)
    (hu : ∀ t : ZMod d, t.val % 2 = 0 → t ≠ s → n t = 0) : degE n = n s := by
  unfold degE
  rw [Finset.sum_eq_single s]
  · rw [if_pos hs]
  · intro t _ hts
    split_ifs with ht
    · exact hu t ht hts
    · rfl
  · intro h
    exact absurd (Finset.mem_univ s) h
end Formalism.DworkPowerSeriesWeights
