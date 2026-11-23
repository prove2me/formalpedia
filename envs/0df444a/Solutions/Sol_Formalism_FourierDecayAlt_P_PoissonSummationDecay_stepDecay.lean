-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.stepDecay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:04.896364+00:00
-- url     : https://prove2.me/submissions/7133bfe7-03bb-4c7f-a990-b0280204857a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (h : PoissonStep) : PoissonStepDecay := by
  intro V _ _ _ _ _ hP Λ _ _ φ b x hc hb h1 h2 hnn S
  exact h V Λ φ x (hP Λ (fun v => (φ v : ℂ)) (Complex.continuous_ofReal.comp hc) b hb h1 h2 x) hnn S
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
