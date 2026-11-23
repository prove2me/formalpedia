-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.tail_haar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:35.868035+00:00
-- url     : https://prove2.me/submissions/225bba4a-4547-4a58-a932-7529796cb061

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_integrable_maxpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_maxpow_scale

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
theorem _root_.solution (ν : Measure E) [ν.IsAddHaarMeasure] (T A : ℝ) (hT : 1 ≤ T)
    (hA : (Module.finrank ℝ E : ℝ) + 1 ≤ A) :
    Integrable (fun q : E => (max T ‖q‖) ^ (-A)) ν ∧
    ∫ q : E, (max T ‖q‖) ^ (-A) ∂ν ≤
      T ^ ((Module.finrank ℝ E : ℝ) - A) * ∫ q : E, (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1)) ∂ν := by
  have hT0 : 0 < T := by linarith
  have hIA : Integrable (fun q : E => (max 1 ‖q‖) ^ (-A)) ν := integrable_maxpow ν A (by linarith)
  have hIB : Integrable (fun q : E => (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1))) ν :=
    integrable_maxpow ν _ (by linarith)
  have hfun : (fun q : E => (max T ‖q‖) ^ (-A)) = fun q : E => T ^ (-A) * (max 1 ‖T⁻¹ • q‖) ^ (-A) :=
    funext fun q => maxpow_scale T A hT0 q
  constructor
  · rw [hfun]
    exact (hIA.comp_smul (inv_ne_zero hT0.ne')).const_mul _
  · rw [hfun, integral_const_mul, Measure.integral_comp_inv_smul ν (fun q : E => (max 1 ‖q‖) ^ (-A)) T,
      abs_of_nonneg (by positivity), smul_eq_mul, ← mul_assoc]
    have e : T ^ ((Module.finrank ℝ E : ℝ) - A) = T ^ (-A) * T ^ (Module.finrank ℝ E) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hT0]; congr 1; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono hIA hIB fun q => ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
