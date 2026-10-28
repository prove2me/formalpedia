-- Prove2me | solution 1 for AvramDividend.Classical.zero_scale_weighted_renewal_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:45:28.930348+00:00
-- url     : https://prove2.me/submissions/27ba1f81-511d-4c4e-a639-de5255c2940f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hqθ : q < X.ψ θ) :
    q * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(θ * y)) * W₀ y ∂volume) < 1 := by
  have hψ : 0 < X.ψ θ := lt_of_le_of_lt hq hqθ
  rw [(hW₀.2.2.2.2 θ hθ (by linarith)).2, sub_zero, ← div_eq_mul_inv, div_lt_one hψ]
  exact hqθ
