-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_dot_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:25.847096+00:00
-- url     : https://prove2.me/submissions/683ecb44-3fef-47cc-8737-53c596bfa39c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_sum
import Theorems.Thm_Formalism_LT_CoeffP_Bd_sum


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
theorem _root_.solution {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (n.degree : ℝ) * c := by
  unfold dot
  rw [Finsupp.sum, ← Finset.sum_mul]
  congr 1
  first
  | simp [Finsupp.degree_apply]
  | simp [Finsupp.degree, Finsupp.sum]
  | (rw [Finsupp.degree_apply]; push_cast; rfl)
end Formalism.DworkPowerSeriesWeights
