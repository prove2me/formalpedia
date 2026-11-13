-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a44_discounted_terminal_spatial_positive_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:55:17.508929+00:00
-- url     : https://prove2.me/submissions/a7fef108-4872-405d-9e24-45de6ee716ec

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_avram_ga_a33_terminal_positive_exponential_majorant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (q θ K L : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (t : Ω → ℝ≥0)
    (w : ℝ → ℝ) (Y Z H : Ω → ℝ)
    (hCells : ∀ᵐ ω ∂ P,
      (Z ω = Y ω) ∨
      (-L ≤ w (Y ω) ∧
        w (Z ω) ≤ K * Real.exp (θ * Z ω) ∧
        Z ω ≤ H ω)) :
    ∀ᵐ ω ∂ P,
      max (Real.exp (-(q * (t ω : ℝ))) *
        (w (Z ω) - w (Y ω))) 0 ≤
      K * Real.exp (θ * H ω) + L := by
  filter_upwards [hCells] with ω hc
  rcases hc with hz | hc
  · have hNonneg : 0 ≤ K * Real.exp (θ * H ω) + L :=
      add_nonneg (mul_nonneg hK (le_of_lt (Real.exp_pos _))) hL
    simpa [hz] using hNonneg
  · rcases hc with ⟨ hLower, hUpper, hZ ⟩
    have hBound :=
      avram_ga_a33_terminal_positive_exponential_majorant
        q θ K L hq hK hL (t ω)
        (w (Z ω)) (w (Y ω)) (Z ω)
        hLower hUpper
    have hExp : Real.exp (θ * Z ω) ≤
        Real.exp (θ * H ω) := by
      exact (Real.exp_le_exp).2 (mul_le_mul_of_nonneg_left hZ hθ)
    have hScaled : K * Real.exp (θ * Z ω) ≤
        K * Real.exp (θ * H ω) :=
      mul_le_mul_of_nonneg_left hExp hK
    have hPlus : K * Real.exp (θ * Z ω) + L ≤
        K * Real.exp (θ * H ω) + L := by
      linarith only [hScaled]
    exact hBound.trans hPlus
