-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_finite_step_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:24:45.467501+00:00
-- url     : https://prove2.me/submissions/7a8300f6-b218-4d5c-baa1-1dd869bc7040

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine reflected reward has a finite right-difference upper budget
at the fixed mesh equal to the positive barrier, without scale derivatives. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (a * W (a + a) / (W (a + a) - W a)) := by
  obtain ⟨hposW, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have ha2 : 0 < a + a := by linarith
  have hWa : 0 ≤ W a := (hposW a ha).le
  have hWright : 0 < W (a + a) := hposW (a + a) ha2
  have hmono' :
      Real.exp (-φ * a) * W a ≤
        Real.exp (-φ * (a + a)) * W (a + a) := by
    exact hmono (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr ha2) (by linarith)
  have hexp :
      Real.exp (-φ * (a + a)) < Real.exp (-φ * a) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos hφ ha]
  have hWinc : W a < W (a + a) := by
    by_contra hnot
    have hWle : W (a + a) ≤ W a := le_of_not_gt hnot
    have hmul1 :
        Real.exp (-φ * (a + a)) * W (a + a) ≤
          Real.exp (-φ * (a + a)) * W a :=
      mul_le_mul_of_nonneg_left hWle (Real.exp_pos _).le
    have hmul2 :
        Real.exp (-φ * (a + a)) * W a <
          Real.exp (-φ * a) * W a :=
      mul_lt_mul_of_pos_right hexp (hposW a ha)
    exact (not_lt_of_ge hmono') (lt_of_le_of_lt hmul1 hmul2)
  obtain ⟨w, hw, hbudget, hstep⟩ :=
    stoppedFirstRecord_upper_geometric_budgets
      X hX q hq W hW a a ha ha hWright hWa hWinc
  apply barrierSupValue_le_right_scale_quotient_of_killed_grid_step
    X W a 0 q a hq.le ha hWright hWa hWinc w
  · intro n ω
    simpa only [zero_add] using hw n ω
  · exact hbudget
  · exact hstep
