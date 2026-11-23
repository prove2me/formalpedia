-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.tail_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:01.128352+00:00
-- url     : https://prove2.me/submissions/ab4d5615-c54d-461f-9440-e2277cf46cd3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_tail_haar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (ν μ : Measure E) [ν.IsAddHaarMeasure] (k : NNReal) (hμ : μ = k • ν) (T A : ℝ) (hT : 1 ≤ T)
    (hA : (Module.finrank ℝ E : ℝ) + 1 ≤ A) :
    Integrable (fun q : E => (max T ‖q‖) ^ (-A)) μ ∧
    ∫ q : E, (max T ‖q‖) ^ (-A) ∂μ ≤
      T ^ ((Module.finrank ℝ E : ℝ) - A) * ∫ q : E, (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1)) ∂μ := by
  obtain ⟨h1, h2⟩ := tail_haar ν T A hT hA
  subst hμ
  refine ⟨h1.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul,
    smul_eq_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h2 k.coe_nonneg
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
