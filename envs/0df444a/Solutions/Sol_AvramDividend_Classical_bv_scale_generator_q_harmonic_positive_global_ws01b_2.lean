-- Prove2me | solution 2 for AvramDividend.Classical.bv_scale_generator_q_harmonic_positive_global_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:36:57.696854+00:00
-- url     : https://prove2.me/submissions/6f79bcb8-9864-48b6-aba9-92feafccb28c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_q_harmonic_all_barriers_ws01b
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have ha : (0 : ℝ) < y + 1 := by linarith
  have hy_mem : y ∈ Ioo (0 : ℝ) (y + 1) := ⟨hy, by linarith⟩
  obtain ⟨hInt, hEq⟩ :=
    AvramDividend.Classical.bv_scale_generator_q_harmonic_all_barriers_ws01b
      X hX q hq W hW hBV (y + 1) ha y hy_mem
  exact ⟨hInt, sub_eq_zero.mp hEq⟩
