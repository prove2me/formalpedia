-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_actual_measure_boundary_forward_secant_positive_part_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:53:35.576225+00:00
-- url     : https://prove2.me/submissions/0e548525-181f-48c4-8ad7-a8de308e1f63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The true dividend Stieltjes measure cannot charge a positive part of the globally
closed-cap forward secant correction. This includes diffuse and singular-continuous
variation and the time-zero atom, without a derivative at either cap endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      ∂(dividendMeasure D ω)) = 0 := by
  have hPoint : ∀ s : ℝ,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) = 0 := by
    intro s
    let y : ℝ := max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)
    have hy : 0 ≤ y := le_max_left _ _
    have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ.le
    have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      y (y + δ) hy hOrder
    have hResidual : δ + V y - V (y + δ) ≤ 0 := by
      linarith only [hSec]
    apply ENNReal.ofReal_eq_zero.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
  have hEq : (fun s : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))) =
      (fun _ : ℝ => (0 : ℝ≥0∞)) := funext hPoint
  simp only [hEq]
  simp
