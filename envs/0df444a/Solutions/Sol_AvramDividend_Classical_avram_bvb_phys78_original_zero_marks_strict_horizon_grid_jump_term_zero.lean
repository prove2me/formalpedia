-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:19:12.461032+00:00
-- url     : https://prove2.me/submissions/fcc9f13b-0784-4edf-bc6c-891aea54b576

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original negative-mark jump integral vanishes for every strict
pre-horizon grid mask, uniformly in the grid index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0)
    (H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hMask : ∀ n (p : ℝ≥0 × ℝ), H n ((p.1, ω), p.2) ≠ 0 →
      0 < p.1 ∧ (p.1 : ℝ) < (T : ℝ) - δ n ∧ p.2 < 0) :
    ∀ n : ℕ,
      (∫ p, H n ((p.1, ω), p.2)
        ∂((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by
  intro n
  apply avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
    X ω T hZero (H n)
  intro p hp
  rcases hMask n p hp with ⟨hpos, hbefore, hneg⟩
  have hbound : (p.1 : ℝ) ≤ (T : ℝ) := by
    linarith [hδ n]
  have hle : p.1 ≤ T := by exact_mod_cast hbound
  exact ⟨⟨hpos, hle⟩, hneg⟩
