-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_degO_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:00.637937+00:00
-- url     : https://prove2.me/submissions/1e0191c0-204d-4ead-b4ec-bd7f79c547e4

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
theorem _root_.solution {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0)
    (hu : ∀ t : ZMod d, t.val % 2 ≠ 0 → t ≠ s → n t = 0) : degO n = n s := by
  unfold degO
  rw [Finset.sum_eq_single s]
  · rw [if_neg hs]
  · intro t _ hts
    split_ifs with ht
    · rfl
    · exact hu t ht hts
  · intro h
    exact absurd (Finset.mem_univ s) h
end Formalism.DworkPowerSeriesWeights
