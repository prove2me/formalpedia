-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.integrable_gK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:40.26564+00:00
-- url     : https://prove2.me/submissions/fe5511a7-9457-43e5-8c48-09d43d2ee096

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_norm_gK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (δ p q : ℝ) (hδ : 0 < δ) : Integrable (gK δ p q) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable (fun z : ℝ × ℝ => Real.exp (-δ * z.1 ^ 2) * Real.exp (-δ * z.2 ^ 2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (integrable_exp_neg_mul_sq hδ).mul_prod (integrable_exp_neg_mul_sq hδ)
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => (norm_gK δ p q z).le)
  have : Continuous (gK δ p q) := by unfold gK; fun_prop
  exact this.aestronglyMeasurable
end Formalism.FourierDecayAlt.P.G8
