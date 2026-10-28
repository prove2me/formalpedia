-- Prove2me | solution 2 for AvramDividend.Classical.bv_inverse_frequency_mesh_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:37:52.680165+00:00
-- url     : https://prove2.me/submissions/fa2e73ed-162d-4640-9845-b04075f337de

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (δ θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθne : ∀ n, θ n ≠ 0)
    (hProduct : ∀ n, δ n * θ n = c) :
    Tendsto (fun n : ℕ =>
      δ n * (X.drift * θ n - X.ψ (θ n)))
      atTop (nhds (0 : ℝ)) := by
  have h := ((AvramDividend.Classical.bv_exponent_gap_div_tendsto_zero X hBV).comp hθ).const_mul c
  rw [mul_zero] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp]
  rw [← hProduct n]
  field_simp [hθne n]
