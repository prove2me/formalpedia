-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.c_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:33.825922+00:00
-- url     : https://prove2.me/submissions/8ee2176b-53fd-4b89-9292-a37df95b4ebd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_c_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_c_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (κ : NNReal) (E' : ℕ) :
    ∃ C : ℝ, ∀ A : ℝ, (E' : ℝ) + (Module.finrank ℝ E : ℝ) + 1 ≤ A →
      Integrable (fun y : E => (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A)) (κ • ν) ∧
      ∫ y : E, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(κ • ν) ≤ C ∧
      ∀ τ : ℝ, 1 ≤ τ →
        ∫ y in {y : E | τ ≤ ‖y‖}, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(κ • ν) ≤
          C * τ ^ ((E' : ℝ) + (Module.finrank ℝ E : ℝ) - A) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Module.finrank ℝ E : ℝ) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ Nat.cast_nonneg _
  obtain ⟨G, hG⟩ : ∃ G : E → ℝ, G = fun y => 2 ^ ((E' : ℝ) + d + 1) * (1 + ‖y‖) ^ (-(d + 1)) := ⟨_, rfl⟩
  have hGi : Integrable G ν := by
    rw [hG]; exact (integrable_one_add_norm (by rw [← hd]; linarith)).const_mul _
  have hG0 : ∀ y, 0 ≤ G y := fun y => by rw [hG]; positivity
  refine ⟨κ * ∫ y, G y ∂ν, fun A hA => ?_⟩
  rw [← hd] at hA ⊢
  obtain ⟨F, hF⟩ : ∃ F : E → ℝ, F = fun y : E => (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) := ⟨_, rfl⟩
  rw [← hF]
  have hF0 : ∀ y : E, 0 ≤ F y := fun y => by rw [hF]; positivity
  have hFG : ∀ y : E, F y ≤ G y := fun y => by
    rw [hF, hG]; exact c_le ‖y‖ (norm_nonneg _) E' d A hd0 hA
  have hFm : Measurable F := by rw [hF]; fun_prop
  have hFi : Integrable F ν :=
    hGi.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hF0 y)]; exact hFG y)
  refine ⟨hFi.smul_measure_nnreal, ?_, fun τ hτ => ?_⟩
  · rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (integral_mono hFi hGi hFG) κ.coe_nonneg
  · have hτ0 : 0 < τ := by linarith
    have hS : MeasurableSet {y : E | τ ≤ ‖y‖} := measurableSet_le measurable_const measurable_norm
    rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ κ.coe_nonneg
    rw [← integral_indicator hS]
    have key := Measure.integral_comp_smul ν ({y : E | τ ≤ ‖y‖}.indicator F) τ
    rw [abs_of_pos (by positivity), smul_eq_mul] at key
    have key2 : ∫ y, {y : E | τ ≤ ‖y‖}.indicator F y ∂ν =
        τ ^ Module.finrank ℝ E * ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν := by
      rw [key]; field_simp
    have bd : ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν ≤ ∫ w, τ ^ ((E' : ℝ) - A) * G w ∂ν := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => Set.indicator_nonneg (fun y _ => hF0 y) _)
        (hGi.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
      have hpos : 0 ≤ τ ^ ((E' : ℝ) - A) := by positivity
      by_cases hw : τ ≤ ‖τ • w‖
      · have hn : ‖τ • w‖ = τ * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hτ0.le]
        have hw1 : 1 ≤ ‖w‖ := by
          rw [hn] at hw
          exact le_of_mul_le_mul_left (by linarith) hτ0
        simp only [Set.indicator_of_mem (show τ • w ∈ {y : E | τ ≤ ‖y‖} from hw)]
        have h1 : F (τ • w) ≤ τ ^ ((E' : ℝ) - A) * F w := by
          rw [hF]; simp only [hn]; exact c_scale ‖w‖ τ hw1 hτ E' A
        exact h1.trans (mul_le_mul_of_nonneg_left (hFG w) hpos)
      · simp only [Set.indicator_of_notMem (show τ • w ∉ {y : E | τ ≤ ‖y‖} from hw)]
        exact mul_nonneg hpos (hG0 w)
    rw [integral_const_mul] at bd
    rw [key2]
    calc τ ^ Module.finrank ℝ E * ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν
        ≤ τ ^ Module.finrank ℝ E * (τ ^ ((E' : ℝ) - A) * ∫ w, G w ∂ν) :=
          mul_le_mul_of_nonneg_left bd (by positivity)
      _ = (∫ w, G w ∂ν) * τ ^ ((E' : ℝ) + d - A) := by
          rw [← Real.rpow_natCast, ← hd, ← mul_assoc, ← Real.rpow_add hτ0, mul_comm]
          congr 2; ring
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
