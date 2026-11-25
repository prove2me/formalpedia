-- Prove2me | solution 2 for Formalism.FourierDecayAlt.P5.integral_nonneg_complex
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T04:27:52.860806+00:00
-- url     : https://prove2.me/submissions/972cb73b-e33a-4866-9b07-122badb643c4

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqOfContinuousOffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

/-- The Bochner integral of a pointwise nonnegative complex-valued function is nonnegative
for the `ComplexOrder` order on `ℂ`. -/
theorem solution {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν :=
  integral_nonneg h
