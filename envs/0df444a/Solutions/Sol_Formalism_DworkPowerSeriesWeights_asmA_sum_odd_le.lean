-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_sum_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:24.736094+00:00
-- url     : https://prove2.me/submissions/1be6309e-e487-4be8-a721-f401c3d7d2ba

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_odd_hasSum

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
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) (N : Finset ℕ) (hN : ∀ n ∈ N, Odd n) :
    ∑ n ∈ N, ((l : ℝ) ^ n)⁻¹ ≤ gam l := by
  calc ∑ n ∈ N, ((l : ℝ) ^ n)⁻¹
      = ∑ n ∈ N, (if Odd n then ((l : ℝ) ^ n)⁻¹ else 0) :=
        Finset.sum_congr rfl fun n hn => by rw [if_pos (hN n hn)]
    _ ≤ gam l := sum_le_hasSum N (fun i _ => by split_ifs <;> positivity) (asmA_odd_hasSum l hl)
end Formalism.DworkPowerSeriesWeights
