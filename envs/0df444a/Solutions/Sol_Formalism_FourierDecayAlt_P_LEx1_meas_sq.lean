-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.meas_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:00.817173+00:00
-- url     : https://prove2.me/submissions/935e4e98-966d-41d2-b356-fdcacb0b6dbf

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
theorem _root_.solution (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (v : Fn B A')
    (h1 : ∀ a, Measurable fun ω => wt ω a) (h2 : ∀ a, Measurable fun ω => v ω a) : Measurable (LE.sq B wt v) := by
  unfold LE.sq
  exact Finset.measurable_sum _ fun a _ => (h1 a).mul ((h2 a).norm.pow_const 2)
end Formalism.FourierDecayAlt.P.LEx1
