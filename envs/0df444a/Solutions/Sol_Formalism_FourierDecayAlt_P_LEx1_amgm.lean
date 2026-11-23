-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.amgm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:30.301863+00:00
-- url     : https://prove2.me/submissions/79f4e303-11d6-4148-8f86-507df9882fc8

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by
  have h := sq_nonneg (a - δ * b)
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ := by field_simp; ring
  have h2 : 0 ≤ (a - δ * b) ^ 2 / δ := by positivity
  linarith
end Formalism.FourierDecayAlt.P.LEx1
