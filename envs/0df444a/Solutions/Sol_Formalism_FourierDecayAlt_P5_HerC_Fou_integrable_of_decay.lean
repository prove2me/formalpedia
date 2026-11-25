-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.integrable_of_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:43.776414+00:00
-- url     : https://prove2.me/submissions/a6959b57-4da2-4a12-88fe-39b5019d020e

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u :=
  ((integrable_one_add_norm (by linarith)).const_mul C).mono' hu.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hdec x)
end Formalism.FourierDecayAlt.P5.HerC.Fou
