-- Prove2me | solution 1 for AvramDividend.Classical.bv_inverse_frequency_mesh_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:37:02.209044+00:00
-- url     : https://prove2.me/submissions/144f2918-3007-4c9a-9ae4-1272aa5d2094

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
  have h := ((bv_exponent_gap_div_tendsto_zero X hBV).comp hθ).const_mul c
  rw [mul_zero] at h
  refine h.congr (fun n => ?_)
  have hd : δ n = c / θ n := eq_div_of_mul_eq (hθne n) (hProduct n)
  simp only [Function.comp_apply, hd]
  field_simp
