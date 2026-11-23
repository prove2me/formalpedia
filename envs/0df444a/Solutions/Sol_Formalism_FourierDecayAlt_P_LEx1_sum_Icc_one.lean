-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.sum_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:42.877424+00:00
-- url     : https://prove2.me/submissions/b32dbfb2-e0d3-4e2d-a6cf-5840ffa1fa7a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull

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
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (f : ℕ → ℝ) (R : ℕ) : ∑ p ∈ Icc 1 R, f p = ∑ i ∈ range R, f (i + 1) := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
end Formalism.FourierDecayAlt.P.LEx1
