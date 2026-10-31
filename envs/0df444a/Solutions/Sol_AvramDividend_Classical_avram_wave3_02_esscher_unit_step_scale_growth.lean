-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_esscher_unit_step_scale_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:18.590243+00:00
-- url     : https://prove2.me/submissions/4f3fa29e-38ff-4a26-ba7f-d2d69e525cc6

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Esscher-normalised monotonicity gives one common strictly exponential
one-unit scale growth factor, at every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ a : ℝ, 0 < a →
      W a ≤ Real.exp (-φ) * W (a + 1) := by
  rcases scaleFunction_tilted_positive_monotone X hX q hq W hW with
    ⟨_, φ, hφ, hmono⟩
  refine ⟨φ, hφ, ?_⟩
  intro a ha
  have hnext : 0 < a + 1 := by linarith
  have hle : a ≤ a + 1 := by linarith
  have hm := hmono ha hnext hle
  have hE : Real.exp (-φ * (a + 1)) =
      Real.exp (-φ * a) * Real.exp (-φ) := by
    rw [show -φ * (a + 1) = (-φ * a) + (-φ) by ring]
    exact Real.exp_add _ _
  change Real.exp (-φ * a) * W a ≤
    Real.exp (-φ * (a + 1)) * W (a + 1) at hm
  rw [hE] at hm
  have he : 0 < Real.exp (-φ * a) := Real.exp_pos _
  by_contra hn
  have hgt : Real.exp (-φ) * W (a + 1) < W a := lt_of_not_ge hn
  have hmullt : Real.exp (-φ * a) * (Real.exp (-φ) * W (a + 1)) <
      Real.exp (-φ * a) * W a := mul_lt_mul_of_pos_left hgt he
  nlinarith [hm, hmullt]
