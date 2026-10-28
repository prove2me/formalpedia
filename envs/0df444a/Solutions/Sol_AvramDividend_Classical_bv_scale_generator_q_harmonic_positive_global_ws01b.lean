-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_generator_q_harmonic_positive_global_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:35:28.928509+00:00
-- url     : https://prove2.me/submissions/bb8d1770-b178-44c7-969e-6087c521a493

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_q_harmonic_all_barriers_ws01b
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable W y ∧ X.generator W y = q * W y := by
  intro y hy
  obtain ⟨h1, h2⟩ := bv_scale_generator_q_harmonic_all_barriers_ws01b X hX q hq W hW hBV (y + 1)
    (by linarith) y ⟨hy, by linarith⟩
  exact ⟨h1, by linarith⟩
