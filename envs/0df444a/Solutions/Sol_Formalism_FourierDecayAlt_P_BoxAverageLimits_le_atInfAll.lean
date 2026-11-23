-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.le_atInfAll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:52.092962+00:00
-- url     : https://prove2.me/submissions/3f2122ae-b26b-4b49-9390-e6bbc6da29b9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (f : ℕ) :
    (⨅ T : ℝ, 𝓟 {x : V f | ∀ v, T ≤ ‖x v‖}) ≤ atInfAll f := by
  unfold atInfAll
  refine le_iInf (fun v => ?_)
  rw [← Filter.tendsto_iff_comap]
  rw [Filter.tendsto_atTop]
  intro T
  exact Filter.mem_iInf_of_mem T (Filter.mem_principal.mpr (fun x hx => hx v))
end Formalism.FourierDecayAlt.P.BoxAverageLimits
