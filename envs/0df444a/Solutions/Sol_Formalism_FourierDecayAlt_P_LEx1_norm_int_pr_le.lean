-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.norm_int_pr_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:23.459168+00:00
-- url     : https://prove2.me/submissions/8fcc36d1-53ca-4b55-9eef-5b1bee4e9b90

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pr_bound

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) (δ : ℝ) (hδ : 0 < δ) :
    ‖∫ ω, pr B wt a b ω ∂B.μ‖ ≤ ((∫ ω, LE.sq B wt a ω ∂B.μ) / δ + δ * ∫ ω, LE.sq B wt b ω ∂B.μ) / 2 := by
  refine (norm_integral_le_of_norm_le (((ha.div_const δ).add (hb.const_mul δ)).div_const 2)
    (Eventually.of_forall fun ω => pr_bound B wt hpos a b δ hδ ω)).trans (le_of_eq ?_)
  rw [integral_div, integral_add' (ha.div_const δ) (hb.const_mul δ), integral_div, integral_const_mul]
end Formalism.FourierDecayAlt.P.LEx1
