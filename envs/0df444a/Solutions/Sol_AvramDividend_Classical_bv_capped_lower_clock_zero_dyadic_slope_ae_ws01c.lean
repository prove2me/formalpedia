-- Prove2me | solution 1 for AvramDividend.Classical.bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:11:58.225277+00:00
-- url     : https://prove2.me/submissions/feda3bfd-d703-4360-9b3d-d31f003d5121

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_capped_raw_lower_clock_NNReal_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_zero_slope_path_event_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation)
    (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) -
          (X.X
            ((twoSidedExitDownTime X lower ω ⊓
              (T : ℝ≥0∞)).toNNReal + ((1 : ℝ≥0) / 2) ^ n) ω -
           X.X
            ((twoSidedExitDownTime X lower ω ⊓
              (T : ℝ≥0∞)).toNNReal) ω)) /
          ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
  let raw : Ω → ℝ≥0 := fun ω =>
    (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞)).toNNReal
  let U : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (raw ω + t) ω - X.X (raw ω) ω
  let V : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let δ : ℕ → ℝ≥0 := fun n => ((1 : ℝ≥0) / 2) ^ n
  let G : Set (ℝ≥0 → ℝ) := {f |
    Tendsto (fun n : ℕ =>
      (X.drift * (δ n : ℝ) - f (δ n)) / (δ n : ℝ))
      atTop (𝓝 (0 : ℝ))}
  have hRawMeas : Measurable raw :=
    bv_capped_raw_lower_clock_NNReal_measurable_ws01c X lower T
  have hU : Measurable U :=
    bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
      X raw hRawMeas
  have hV : Measurable V := levy_wholePath_measurable X
  have hLaw : Measure.map U P = Measure.map V P :=
    bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
      X lower T mesh M hpos hzero hCover
  have hG : MeasurableSet G :=
    bv_dyadic_zero_slope_path_event_measurable_ws01c
      X.drift δ
  have hOriginal : ∀ᵐ ω ∂P, V ω ∈ G := by
    change ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) -
          X.X (((1 : ℝ≥0) / 2) ^ n) ω) /
            ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ))
        atTop (𝓝 (0 : ℝ))
    exact bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c X hBV
  have hTransferred : ∀ᵐ ω ∂P, U ω ∈ G := by
    apply (ae_iff).2
    calc
      P {ω | ¬ U ω ∈ G} = P (U ⁻¹' Gᶜ) := by rfl
      _ = (Measure.map U P) Gᶜ :=
        (Measure.map_apply hU hG.compl).symm
      _ = (Measure.map V P) Gᶜ := by rw [hLaw]
      _ = P (V ⁻¹' Gᶜ) := Measure.map_apply hV hG.compl
      _ = P {ω | ¬ V ω ∈ G} := by rfl
      _ = 0 := (ae_iff).1 hOriginal
  change ∀ᵐ ω ∂P, U ω ∈ G
  exact hTransferred