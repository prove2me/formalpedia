-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.meas_pr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:09.973796+00:00
-- url     : https://prove2.me/submissions/86e5040b-a65c-44ad-a902-59c5cc67d4c5

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i) :
    Measurable (pr B wt a b) := by
  unfold pr
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((Complex.measurable_ofReal.comp (h0 i)).mul (h1 i)).mul (Complex.continuous_conj.measurable.comp (h2 i))
end Formalism.FourierDecayAlt.P.LEx1
