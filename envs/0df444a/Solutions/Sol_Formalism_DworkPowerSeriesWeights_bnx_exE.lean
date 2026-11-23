-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_exE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:01.208354+00:00
-- url     : https://prove2.me/submissions/3cc7c6a6-97a5-46a7-9bdd-8b430d9bab21

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
theorem _root_.solution {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degE n) :
    ∃ s : ZMod d, s.val % 2 = 0 ∧ n s ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h0 : degE n = 0 := by
    unfold degE
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · exact hne s hs
    · rfl
  omega
end Formalism.DworkPowerSeriesWeights
