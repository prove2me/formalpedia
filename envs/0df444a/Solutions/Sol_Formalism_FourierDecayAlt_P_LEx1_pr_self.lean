-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.pr_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:31.092383+00:00
-- url     : https://prove2.me/submissions/4c7bec7c-e343-4e91-994e-f2572e92d25c

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (ω : B.Ω) :
    pr B wt v v ω = ((LE.sq B wt v ω : ℝ) : ℂ) := by
  simp only [pr, LE.sq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp
end Formalism.FourierDecayAlt.P.LEx1
