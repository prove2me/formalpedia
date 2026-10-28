-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_finite_horizon_null_events_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:19:50.97471+00:00
-- url     : https://prove2.me/submissions/8d6c0126-9222-422b-bcd1-4d2e861d083d

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Process.Adapted
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (θ : ℝ) (A : Set Ω) :
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) A = 0 ↔ P A = 0 := by
  have hm : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hf : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))) := by fun_prop
  rw [withDensity_apply_eq_zero hf]
  have : {x | ENNReal.ofReal (Real.exp (θ * X.X t x - (t : ℝ) * X.ψ θ)) ≠ 0} = univ := by
    ext x; simp [Real.exp_pos]
  rw [this, univ_inter]
