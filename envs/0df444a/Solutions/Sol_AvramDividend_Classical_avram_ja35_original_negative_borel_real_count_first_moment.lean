-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja35_original_negative_borel_real_count_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:33:47.134198+00:00
-- url     : https://prove2.me/submissions/1ee3f54b-1670-4b3b-8bd5-fec9ea756b87

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Convert the exact physical negative-Borel Campbell mean into an integrable real mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) =
        ((T : ℝ≥0∞) * X.ν B).toReal := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change Integrable (fun ω => (N ω).toReal) P ∧
    (∫ ω, (N ω).toReal ∂P) =
      ((T : ℝ≥0∞) * X.ν B).toReal
  have hMeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X 0 T zero_le B hB
  have hRate : (∫⁻ ω, N ω ∂P) =
      (T : ℝ≥0∞) * X.ν B := by
    simpa [N] using avram_ja34_original_all_negative_borel_expected_count_exact
      X T B hB hNeg
  have hNu : X.ν B ≠ ⊤ := by
    have hb := measure_mono hNeg (μ := X.ν)
    exact ne_of_lt (lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hFinite))
  have hRateFin : ((T : ℝ≥0∞) * X.ν B) ≠ ⊤ :=
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
