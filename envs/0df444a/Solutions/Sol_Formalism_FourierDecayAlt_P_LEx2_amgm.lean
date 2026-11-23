-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.amgm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:47.986924+00:00
-- url     : https://prove2.me/submissions/5f064bc1-37d7-4aa5-89cd-dc64a6a03f40

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by
  have h := sq_nonneg (a - δ * b)
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ := by field_simp; ring
  have h2 : 0 ≤ (a - δ * b) ^ 2 / δ := by positivity
  linarith
end Formalism.FourierDecayAlt.P.LEx2
