-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.int_pr_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:02.903815+00:00
-- url     : https://prove2.me/submissions/65b1503f-dcba-45d8-ab92-254ec7457f6f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pr_self

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by
  simp_rw [pr_self]; exact integral_ofReal
end Formalism.FourierDecayAlt.P.LEx1
