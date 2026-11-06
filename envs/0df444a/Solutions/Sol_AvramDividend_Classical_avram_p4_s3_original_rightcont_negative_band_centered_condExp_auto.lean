-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_rightcont_negative_band_centered_condExp_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:46:08.142379+00:00
-- url     : https://prove2.me/submissions/7c67952d-8c1d-4865-beaa-6eaad89bb7f7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Right-continuous finite-band centring from the original Lévy jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (r : ℕ → ℝ≥0)
    (hsr : ∀ k, s < r k) (hrt : ∀ k, r k ≤ t)
    (hShort : Filter.Tendsto (fun k => r k - s) atTop (𝓝 0))
    (hLong : Filter.Tendsto (fun k => t - r k) atTop (𝓝 (t - s)))
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    let J : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    P[(fun ω => (J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  change P[(fun ω => (J s t ω).toReal -
    (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) | 𝓕.rightCont s] =ᵐ[P] 0
  have hFinite : X.ν B ≠ ⊤ :=
    ne_of_lt (avram_p2_a_zero_rate_separated_borel_nu_finite X B hB ε hε hBsep)
  have hMass : ∀ C : Set Ω,
      MeasurableSet[𝓕.rightCont s] C → P C ≠ ⊤ := by
    intro C _
    exact ne_of_lt (measure_lt_top P C)
  have hRate : ∀ k, (∫⁻ ω, J s (r k) ω ∂P) =
      ((r k - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro k
    exact avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
      X s (r k) (le_of_lt (hsr k)) B hB ε hε hBsep
  have hRaw : ∀ (a b : ℝ≥0) (C : Set Ω), a ≤ b →
      MeasurableSet[𝓕 a] C →
      (∫⁻ ω in C, J a b ω ∂P) =
        P C * ((b - a : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro a b C hab hC
    exact avram_p4_s3_original_future_negative_borel_rectangle_all_cells
      X B hB ε hε hBsep a b hab C hC
  have hJmeas : Measurable (J s t) :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s t ×ˢ B) (measurableSet_Ioc.prod hB)
  have hFullRate : (∫⁻ ω, J s t ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B :=
    avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
      X s t hst B hB ε hε hBsep
  exact avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
    X s t r hsr hrt B hB J (fun _ _ _ => rfl) hShort hLong
      hFinite hMass hRate hRaw hJmeas hFullRate
