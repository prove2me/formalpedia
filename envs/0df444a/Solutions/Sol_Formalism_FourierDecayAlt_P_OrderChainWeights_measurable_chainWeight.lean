-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderChainWeights.measurable_chainWeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:37.786584+00:00
-- url     : https://prove2.me/submissions/4cfd56fc-5ed6-48ce-99e5-807055a885c4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.OrderChainWeights
theorem _root_.solution {X : Type} [MeasurableSpace X] (nrm : X → ℝ≥0∞) (hn : Measurable nrm)
    (i : ℕ) : Measurable (chainWeight nrm i) := by
  unfold chainWeight
  refine Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases hjl : (j : ℕ) < l
  · simp only [hjl, if_true]
    exact (hn.comp (measurable_pi_apply j)).pow_const 2
  · simp only [hjl, if_false]
    exact measurable_const
end Formalism.FourierDecayAlt.P.OrderChainWeights
