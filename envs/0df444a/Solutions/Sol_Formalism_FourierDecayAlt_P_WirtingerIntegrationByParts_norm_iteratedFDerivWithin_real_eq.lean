-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_iteratedFDerivWithin_real_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:34.234106+00:00
-- url     : https://prove2.me/submissions/30910983-eb9c-4a29-980b-ee38b881cc15

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {s : Set E} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℂ n f s) {x : E} (hx : x ∈ s) {j : ℕ} (hj : j ≤ n) :
    ‖iteratedFDerivWithin ℝ j f s x‖ = ‖iteratedFDerivWithin ℂ j f s x‖ := by
  have h1 := (hf.ftaylorSeriesWithin hs.uniqueDiffOn).restrictScalars ℝ
  have h2 := h1.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j) (by exact_mod_cast hj) hs.uniqueDiffOn hx
  rw [← h2]
  exact ContinuousMultilinearMap.norm_restrictScalars _
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
