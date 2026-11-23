-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.pr_mulF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:08.272985+00:00
-- url     : https://prove2.me/submissions/76789928-da86-4e2f-893b-c8b5c62546a3

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by
  simp only [pr, mulF, Finset.mul_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring
end Formalism.FourierDecayAlt.P.LEx2
