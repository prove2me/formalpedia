-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_uniform_boundary_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:47:55.491754+00:00
-- url     : https://prove2.me/submissions/b7a9d857-95b6-486e-a94e-445b80ce2ebb

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_boundary_reward_of_unit_gap
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under the original Standing law, all genuine reflected Stieltjes
barrier rewards share one finite positive upper bound independent of cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a →
      barrierSupValue X a q ≤ ENNReal.ofReal C := by
  obtain ⟨_, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hstep : ∀ a : ℝ, 0 < a →
      W a ≤ Real.exp (-φ) * W (a + 1) := by
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
  refine ⟨1 / c, div_pos one_pos hc, ?_⟩
  exact avram_wave3_02_uniform_boundary_reward_of_unit_gap
    X hX q hq W hW c hc hgap
