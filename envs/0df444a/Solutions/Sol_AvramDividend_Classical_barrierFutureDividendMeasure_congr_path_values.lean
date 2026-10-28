-- Prove2me | solution 1 for AvramDividend.Classical.barrierFutureDividendMeasure_congr_path_values
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:14:24.972729+00:00
-- url     : https://prove2.me/submissions/1778e554-7974-4a06-a58e-e0815385402e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁]
    [mΩ₂ : MeasurableSpace Ω₂]
    (D : ℝ≥0 → Ω₁ → ℝ) (E : ℝ≥0 → Ω₂ → ℝ)
    (ω₁ : Ω₁) (ω₂ : Ω₂)
    (hvalues : ∀ t : ℝ≥0, D t ω₁ = E t ω₂) :
    dividendMeasure D ω₁ = dividendMeasure E ω₂ := by
  have hfun : (fun t : ℝ => D t.toNNReal ω₁) = fun t => E t.toNNReal ω₂ :=
    funext fun t => hvalues _
  unfold dividendMeasure
  split_ifs with h1 h2 h2
  · have : h1.stieltjesFunction = h2.stieltjesFunction := by
      ext x; simp only [Monotone.stieltjesFunction_eq, hfun]
    rw [this]
  · exact absurd (hfun ▸ h1) h2
  · exact absurd (hfun ▸ h2) h1
  · rfl
