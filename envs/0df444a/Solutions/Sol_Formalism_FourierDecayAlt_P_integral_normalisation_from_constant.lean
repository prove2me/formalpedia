-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integral_normalisation_from_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:52.580132+00:00
-- url     : https://prove2.me/submissions/54bad4e3-a0b6-4827-a4a8-82e2e857e4b1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Nm_exists_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.IntNormFromConst := by
  intro hC k r z z' μsec μG μW μN μW' hD
  obtain ⟨C, hC0, hCf⟩ := hC k r z z' μsec μG μW μN μW' hD
  have hG := hD.haarG
  obtain ⟨K, hKc, hK0⟩ := Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm.exists_pos μG hG.ne_zero
  have hKfin : μG K < ∞ := hG.finite_compact K hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC0.ne'
  refine ⟨C⁻¹, ⟨inv_pos.2 hC0, fun f hf => ?_⟩, ?_⟩
  · rw [lintegral_smul_measure, hCf f hf]
    show ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [← mul_assoc, ENNReal.coe_inv hC0.ne', ENNReal.inv_mul_cancel hCne ENNReal.coe_ne_top, one_mul]
  · rintro c ⟨hc0, hcF⟩
    have hmeas : Measurable (K.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hKm
    have h1 := hcF _ hmeas
    have h2 := hCf _ hmeas
    rw [lintegral_smul_measure, lintegral_indicator_one hKm] at h1
    rw [lintegral_indicator_one hKm] at h2
    rw [h2] at h1
    have key : ∀ X : ℝ≥0∞, μG K = (C : ℝ≥0∞) * X → c • ((C : ℝ≥0∞) * X) = X → c = C⁻¹ := by
      intro X hX hcX
      have hcX' : (c : ℝ≥0∞) * ((C : ℝ≥0∞) * X) = X := hcX
      have hX0 : X ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hX
        exact hK0 hX
      have hXt : X ≠ ∞ := by
        rintro rfl
        rw [ENNReal.mul_top hCne] at hX
        exact hKfin.ne hX
      have hcC : (c : ℝ≥0∞) * C = 1 := by
        calc (c : ℝ≥0∞) * C = (c : ℝ≥0∞) * C * (X * X⁻¹) := by
              rw [ENNReal.mul_inv_cancel hX0 hXt, mul_one]
          _ = ((c : ℝ≥0∞) * (C * X)) * X⁻¹ := by ring
          _ = X * X⁻¹ := by rw [hcX']
          _ = 1 := ENNReal.mul_inv_cancel hX0 hXt
      have hcC' : c * C = 1 := by exact_mod_cast hcC
      exact eq_inv_of_mul_eq_one_left hcC'
    exact key _ h2 h1
end Formalism.FourierDecayAlt.P
