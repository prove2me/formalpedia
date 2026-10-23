-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_stopped_scale_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T06:07:09.62002+00:00
-- url     : https://prove2.me/submissions/4bf1070f-2dec-4fa9-a349-f48096009213

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) := by
  obtain ⟨h1, h2⟩ := AvramDividend.Classical.chat03_grid_stopped_reserve_time_measurable
    X clock H hH lower upper m K hK
  have hWm := AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  exact ((h2.const_mul q).neg.exp).mul (hWm.comp (h1.const_add x))
