-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_negative_count_compensated_L1_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:17:51.884521+00:00
-- url     : https://prove2.me/submissions/95922d3e-bef5-424a-b3c6-52587e9d9c67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hHadapt : Measurable[𝓕 s] H)
    (hHm : Measurable H)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (N : Ω → ℝ≥0∞)
    (hN : ∀ ω : Ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ ω : Ω,
      N ω = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (hJm : AEMeasurable (fun ω => H ω * N ω) P)
    (hJae : ∀ᵐ ω ∂P, H ω * N ω < ⊤)
    (hKae : ∀ᵐ ω ∂P,
      H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) < ⊤)
    (hKfin : (∫⁻ ω, H ω *
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) ∂P) < ⊤) :
    Integrable (fun ω =>
      (H ω * N ω).toReal -
      (H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))).toReal) P ∧
    (∫ ω, ((H ω * N ω).toReal -
      (H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))).toReal) ∂P) = 0 := by
  let rate : ℝ≥0∞ :=
    (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))
  have hComp :=
    avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
      X hBV hFinite s t hst H hHadapt F hF
      (fun ω => (hN ω).symm.trans (hExtract ω))
  have hCompN : (∫⁻ ω, H ω * N ω ∂P) =
      (∫⁻ ω, H ω ∂P) *
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa only [hN] using hComp
  have hKmeas : AEMeasurable (fun ω => H ω * rate) P :=
    (hHm.mul_const rate).aemeasurable
  have hEN : (∫⁻ ω, H ω * N ω ∂P) =
      (∫⁻ ω, H ω * rate ∂P) := by
    rw [lintegral_mul_const rate hHm]
    simpa only [rate, mul_assoc] using hCompN
  have hJfin : (∫⁻ ω, H ω * N ω ∂P) < ⊤ := by
    rw [hEN]
    exact hKfin
  have hJne : ∀ᵐ ω ∂P, H ω * N ω ≠ ⊤ := by
    filter_upwards [hJae] with ω hω
    exact ne_of_lt hω
  have hKne : ∀ᵐ ω ∂P, H ω * rate ≠ ⊤ := by
    filter_upwards [hKae] with ω hω
    exact ne_of_lt hω
  have hJI : Integrable (fun ω => (H ω * N ω).toReal) P :=
    (integrable_toReal_iff hJm hJne).2 (ne_of_lt hJfin)
  have hKI : Integrable (fun ω => (H ω * rate).toReal) P :=
    (integrable_toReal_iff hKmeas hKne).2 (ne_of_lt hKfin)
  have hEreal :
      (∫ ω, (H ω * N ω).toReal ∂P) =
        (∫ ω, (H ω * rate).toReal ∂P) := by
    rw [integral_toReal hJm hJae, integral_toReal hKmeas hKae, hEN]
  change Integrable (fun ω =>
    (H ω * N ω).toReal - (H ω * rate).toReal) P ∧
    (∫ ω, (H ω * N ω).toReal -
      (H ω * rate).toReal ∂P) = 0
  constructor
  · exact hJI.sub hKI
  · rw [integral_sub hJI hKI, hEreal, sub_self]
