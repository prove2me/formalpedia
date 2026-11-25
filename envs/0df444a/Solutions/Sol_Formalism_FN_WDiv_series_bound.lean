-- Prove2me | solution 1 for Formalism.FN.WDiv.series_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:30:37.215018+00:00
-- url     : https://prove2.me/submissions/fc3b3ef5-93c8-4055-a2f5-7182593ed662

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
open Formalism Formalism.FN Formalism.FN.WDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.FN.WDiv
theorem _root_.solution (u : ℕ → ℕ → K) {r : ℝ} (hr : 0 < r) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖u i j‖ * r ^ j ≤ C) : ‖∑' i, u i j‖ * r ^ j ≤ C := by
  rw [← le_div_iff₀ (pow_pos hr j)]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    fun i => (le_div_iff₀ (pow_pos hr j)).2 (h i)
end Formalism.FN.WDiv
