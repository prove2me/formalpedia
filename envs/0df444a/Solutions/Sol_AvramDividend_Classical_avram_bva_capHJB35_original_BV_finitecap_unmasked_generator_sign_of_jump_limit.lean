-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:05:41.36674+00:00
-- url     : https://prove2.me/submissions/e4d2abe6-8423-4e65-a9f5-a51134cc6777

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- The finite-cap boundary generator sign follows from the original
interior HJB inequality by retaining the full negative-jump integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFin : C ≠ ⊤)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℕ → ℝ)
    (hy : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (hwLimit : Tendsto (fun n => w (y n)) atTop (𝓝 (w C.toReal)))
    (hJumpLimit : Tendsto (fun n =>
      ∫ z in Iio (0 : ℝ), w (y n + z) - w (y n) ∂X.ν)
      atTop (𝓝 (∫ z in Iio (0 : ℝ),
        w (C.toReal + z) - w C.toReal ∂X.ν))) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by
  let J : ℝ → ℝ := fun r =>
    ∫ z in Iio (0 : ℝ), w (r + z) - w r ∂X.ν
  have hd : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  have hUpper (n : ℕ) :
      X.drift + J (y n) - q * w (y n) ≤ 0 := by
    have hgi := (hwGen (y n) (hy n).1 (hy n).2).1
    have hΓ := (hwGen (y n) (hy n).1 (hy n).2).2
    rw [boundedVariation_generator_physical_drift_representation
      X hBV w (y n) hgi] at hΓ
    have hSlope := hwGrad (y n) (hy n).1 (hy n).2
    have hProd : X.drift ≤ X.drift * deriv w (y n) := by
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hSlope)]
    dsimp [J]
    linarith
  have hj : Tendsto (fun n => J (y n)) atTop (𝓝 (J C.toReal)) := by
    simpa only [J] using hJumpLimit
  have hq : Tendsto (fun n => q * w (y n))
      atTop (𝓝 (q * w C.toReal)) :=
    tendsto_const_nhds.mul hwLimit
  have hT : Tendsto (fun n : ℕ =>
      X.drift + J (y n) - q * w (y n)) atTop
      (𝓝 (X.drift + J C.toReal - q * w C.toReal)) := by
    convert (tendsto_const_nhds.add hj).sub hq using 1 <;>
      simp only [Function.comp_apply]
  change X.drift + J C.toReal - q * w C.toReal ≤ 0
  exact le_of_tendsto hT (Filter.Eventually.of_forall hUpper)
