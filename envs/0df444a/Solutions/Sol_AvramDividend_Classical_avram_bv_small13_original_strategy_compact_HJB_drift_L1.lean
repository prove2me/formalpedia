-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_small13_original_strategy_compact_HJB_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:12:56.743602+00:00
-- url     : https://prove2.me/submissions/2fb04a75-44ce-4df6-a100-93c3057235e8

import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Compact original BV discounted HJB drift is integrable for the original
dividend strategy, without shifted-surplus admissibility. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(T : ℝ≥0) (x : ℝ)
(D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0)
(q : ℝ) (hq : 0 ≤ q)
(a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
(hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
    (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
     (∫ z in Set.Iio (0 : ℝ),
        w ((Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
     q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  let H : ℝ → ℝ := fun y =>
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y
  have hwMeas := avram_p3_e_compensator_original_ruin_extension_value_measurable
    w hw_cont hw_neg
  have hSigma := avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X
  have hJumpMeas :=
    avram_p3_e_compensator_original_negative_jump_generator_measurable
      X hSigma w hwMeas
  have hHMeas : Measurable H := by
    exact ((measurable_const.mul (measurable_deriv w)).add hJumpMeas).sub
      (measurable_const.mul hwMeas)
  have hUmeas :=
    avram_integration_sweep9_original_controlled_prestate_ambient_measurable
      X x D hD
  have hEmeas :=
    avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
      E hEm
  have hFm :=
    avram_p3_e_compensator_original_discounted_HJB_drift_measurable
      X T x D q E hEmeas hUmeas H hHMeas
  obtain ⟨K, hK, hBound⟩ :=
    avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
      X hBV w hwMeas q a b L R A
      ha ha2 hab hL hR hA hLip hWbound hDeriv
  exact avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
    X T x D q hq E a b K hK H hEregion hBound hFm
