-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:08.267067+00:00
-- url     : https://prove2.me/submissions/c908933c-765f-4042-b3ad-83b1f5d08479

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
theorem _root_.solution {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (L : W →L[ℝ] W') {f : E → W} {s : Set E} {x : E} {n : ℕ} {A P c : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (_hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hL : ‖L‖ ≤ c) (bf : Bd f s x n A P) :
    Bd (fun y => L (f y)) s x n (c * A) P := by
  intro j hj
  have h1 := L.norm_iteratedFDerivWithin_comp_left (hf.contDiffWithinAt hx) hs.uniqueDiffOn hx
    (n := j) (by exact_mod_cast hj)
  have h2 : ‖iteratedFDerivWithin ℝ j (fun y => L (f y)) s x‖ ≤ ‖L‖ * ‖iteratedFDerivWithin ℝ j f s x‖ := h1
  refine h2.trans ?_
  rw [mul_assoc]
  exact mul_le_mul hL (bf j hj) (norm_nonneg _) ((norm_nonneg _).trans hL)
end Bd
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
