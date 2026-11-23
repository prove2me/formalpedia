-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.exists_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:11.273798+00:00
-- url     : https://prove2.me/submissions/63b268fc-8a8a-4653-bc70-50f68ea97584

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution : ∃ f : SchwartzMap ℂ ℂ, f 0 = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x : ℂ => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  have : b 0 = 1 := b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)
  simp [this]
end Formalism.FourierDecayAlt.P.G3
