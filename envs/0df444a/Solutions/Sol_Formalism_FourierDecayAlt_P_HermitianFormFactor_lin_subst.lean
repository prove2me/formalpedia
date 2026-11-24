-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.lin_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:24:25.464966+00:00
-- url     : https://prove2.me/submissions/099c9392-af79-420b-96f7-177d1c4cc346

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : E →ₗ[ℝ] E) (h : L ∘ₗ L' = LinearMap.id) :
    ∃ c : ℝ≥0∞, ∀ f : E → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = c * ∫⁻ x, f (L x) ∂μ := by
  have hdet : LinearMap.det L ≠ 0 := by
    have h1 := congrArg LinearMap.det h
    rw [LinearMap.det_comp, LinearMap.det_id] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨ENNReal.ofReal |LinearMap.det L|, fun f hf => ?_⟩
  rw [← lintegral_map hf (LinearMap.continuous_of_finiteDimensional L).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hdet, abs_one, ENNReal.ofReal_one, one_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
