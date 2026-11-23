-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.int_pr_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:45.877816+00:00
-- url     : https://prove2.me/submissions/6df2db4f-fdc9-4a38-8487-df1baabac924

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_self

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by
  simp_rw [pr_self]; exact integral_ofReal
end Formalism.FourierDecayAlt.P.LEx2
