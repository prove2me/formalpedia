-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_actual_stieltjes_integrable_forward_secant_real_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:00:57.05454+00:00
-- url     : https://prove2.me/submissions/e0d15169-91c0-4aa4-9184-92aec80d37d7

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The true dividend Stieltjes measure has a nonpositive integrable real signed
forward-secant correction, including diffuse, singular-continuous and time-zero
variation, without differentiating the candidate at either cap endpoint. -/
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
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Icc (0 : ℝ) (T : ℝ),
      Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by
  have hPoint : ∀ s : ℝ, Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ≤ 0 := by
    intro s
    let y : ℝ := max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)
    have hy : 0 ≤ y := le_max_left _ _
    have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ.le
    have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      y (y + δ) hy hOrder
    have hResidual : δ + V y - V (y + δ) ≤ 0 := by
      linarith only [hSec]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
  exact MeasureTheory.integral_nonpos_of_ae (Filter.Eventually.of_forall hPoint)
