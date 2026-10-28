-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_uniform_grid_active_expected_le_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:19:25.817297+00:00
-- url     : https://prove2.me/submissions/f48a95e1-a066-4ebd-b428-9f0a5647fa9b

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_uniform_active_expected_le_intensity
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal

/-- The actual finite-activity Levy residual has uniformly bounded expected active grid cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (ts : ℕ → ℝ≥0) (N : ℕ) (hN : 0 < N)
    (T : ℝ)
    (hStep : ∀ i : ℕ, i < N → ts i ≤ ts (i + 1))
    (hMesh : ∀ i : ℕ, i < N →
      (((ts (i + 1) - ts i : ℝ≥0) : ℝ) = T / (N : ℝ))) :
    (∫⁻ ω, ∑ i ∈ range N,
      ({ω : Ω | 0 <
        ((ts (i + 1) : ℝ) * X.drift - X.X (ts (i + 1)) ω) -
          ((ts i : ℝ) * X.drift - X.X (ts i) ω)}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂P) ≤
      ENNReal.ofReal ((X.ν (Iio (0 : ℝ))).toReal * T) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let E : ℕ → Set Ω := fun i => {ω : Ω | 0 <
    ((ts (i + 1) : ℝ) * X.drift - X.X (ts (i + 1)) ω) -
      ((ts i : ℝ) * X.drift - X.X (ts i) ω)}
  have hE (i : ℕ) (_ : i < N) : MeasurableSet (E i) := by
    change MeasurableSet ((fun ω : Ω =>
      ((ts (i + 1) : ℝ) * X.drift - X.X (ts (i + 1)) ω) -
      ((ts i : ℝ) * X.drift - X.X (ts i) ω)) ⁻¹' Ioi 0)
    exact ((measurable_const.sub (X.adapted.measurable)).sub
      (measurable_const.sub (X.adapted.measurable))) measurableSet_Ioi
  have hp (i : ℕ) (hi : i < N) :
      P.real (E i) =
        1 - Real.exp (-((X.ν (Iio (0 : ℝ))).toReal * T / (N : ℝ))) := by
    have h := bv_actual_residual_increment_positive_probability
      X hBV hFinite (ts i) (ts (i + 1)) (hStep i hi)
    change P.real (E i) = _ at h
    rw [hMesh i hi] at h
    convert h using 1 <;> ring
  exact bv_dyadic_uniform_active_expected_le_intensity P E N hN
    (X.ν (Iio (0 : ℝ))).toReal T hE hp
