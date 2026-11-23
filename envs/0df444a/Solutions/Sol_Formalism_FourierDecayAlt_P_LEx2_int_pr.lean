-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.int_pr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:18.975683+00:00
-- url     : https://prove2.me/submissions/53cf2068-2802-4b95-bed0-1f48e4d84b3c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_pr

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
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) : Integrable (pr B wt a b) B.μ := by
  refine Integrable.mono' (((ha.div_const 1).add (hb.const_mul 1)).div_const 2)
    (meas_pr B wt a b h0 h1 h2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  exact pr_bound B wt hpos a b 1 one_pos ω
end Formalism.FourierDecayAlt.P.LEx2
