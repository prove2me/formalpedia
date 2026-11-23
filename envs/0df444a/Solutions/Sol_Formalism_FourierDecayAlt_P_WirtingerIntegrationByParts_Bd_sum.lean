-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:14.700498+00:00
-- url     : https://prove2.me/submissions/1af24e5a-955b-467e-98e6-3ffb5e847a3b

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
namespace Bd
theorem _root_.solution {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : Finset ι) {f : ι → E → W} {A : ι → ℝ}
    {s : Set E} {x : E} {n : ℕ} {P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ∀ i ∈ u, ContDiffOn ℝ n (f i) s) (bf : ∀ i ∈ u, Bd (f i) s x n (A i) P) :
    Bd (fun y => ∑ i ∈ u, f i y) s x n (∑ i ∈ u, A i) P := by
  intro j hj
  have e0 : (fun y => ∑ i ∈ u, f i y) = ∑ i ∈ u, f i := by
    funext y; rw [Finset.sum_apply]
  rw [e0, iteratedFDerivWithin_sum_apply hs.uniqueDiffOn hx
    (fun i hi => ((hf i hi).of_le (by exact_mod_cast hj)).contDiffWithinAt hx), Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => bf i hi j hj)
end Bd
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
