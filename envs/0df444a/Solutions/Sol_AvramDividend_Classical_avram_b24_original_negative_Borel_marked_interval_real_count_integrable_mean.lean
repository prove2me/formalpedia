-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:46:20.36239+00:00
-- url     : https://prove2.me/submissions/a0ad05dc-9178-4a80-b38f-95f7703cfd69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  change Integrable (fun ω => (N ω).toReal) P ∧
    (∫ ω, (N ω).toReal ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  have hMeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  have hRate : (∫⁻ ω, N ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [N] using
      AvramDividend.Classical.avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
        X s t hst B hB hNeg
  have hNu : X.ν B ≠ ⊤ := by
    have hb := measure_mono hNeg (μ := X.ν)
    exact ne_of_lt (lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hFinite))
  have hRateFin : (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hNu
  have hLin : (∫⁻ ω, N ω ∂P) ≠ ⊤ := by
    rw [hRate]
    exact hRateFin
  have hInt : Integrable (fun ω => (N ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hLin
  have hAe : ∀ᵐ ω ∂P, N ω < ⊤ := ae_lt_top hMeas hLin
  have hRealMean :
      (∫ ω, (N ω).toReal ∂P) = (∫⁻ ω, N ω ∂P).toReal :=
    integral_toReal hMeas.aemeasurable hAe
  exact ⟨hInt, hRealMean.trans (congrArg ENNReal.toReal hRate)⟩
