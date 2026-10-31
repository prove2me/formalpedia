-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_uniform_deriv_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:10:31.839516+00:00
-- url     : https://prove2.me/submissions/c2da54d7-1fab-4b0a-a64b-9e009e335411

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_unit_step_scale_growth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_lower_of_unit_gap
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source q-scale derivative has one positive lower growth
coefficient at every positive differentiability point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → DifferentiableAt ℝ W a →
      c * W a ≤ deriv W a := by
  obtain ⟨φ, hφ, hstep⟩ :=
    avram_wave3_02_esscher_unit_step_scale_growth X hX q hq W hW
  have hneg : -φ < (0 : ℝ) := by linarith
  have hexp : Real.exp (-φ) < 1 := by
    have h := Real.exp_strictMono hneg
    simpa only [Real.exp_zero] using h
  let c : ℝ := 1 - Real.exp (-φ)
  have hc : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr hexp
  have hgap : ∀ a : ℝ, 0 < a →
      c * W (a + 1) ≤ W (a + 1) - W a := by
    intro a ha
    have hh := hstep a ha
    dsimp [c]
    nlinarith [hh]
  exact ⟨c, hc, avram_wave3_02_deriv_lower_of_unit_gap
    X hX q hq W hW c hc hgap⟩
