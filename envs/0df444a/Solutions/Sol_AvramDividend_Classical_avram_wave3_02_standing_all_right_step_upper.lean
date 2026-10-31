-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_all_right_step_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:31:07.382203+00:00
-- url     : https://prove2.me/submissions/9c3c9591-7710-4d7f-a6b1-e2909b1ad347

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

/-- At every positive right-hand mesh, the true reflected dividend reward
satisfies the exact finite-difference renewal upper bound, with no C1 input. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ ε : ℝ, 0 < ε →
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  intro ε hε
  obtain ⟨hposW, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have haε : 0 < a + ε := by linarith
  have hWa : 0 ≤ W a := (hposW a ha).le
  have hWright : 0 < W (a + ε) := hposW (a + ε) haε
  have hmono' :
      Real.exp (-φ * a) * W a ≤
        Real.exp (-φ * (a + ε)) * W (a + ε) := by
    exact hmono (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr haε) (by linarith)
  have hexp :
      Real.exp (-φ * (a + ε)) < Real.exp (-φ * a) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos hφ hε]
  have hWinc : W a < W (a + ε) := by
    by_contra hnot
    have hWle : W (a + ε) ≤ W a := le_of_not_gt hnot
    have hmul1 :
        Real.exp (-φ * (a + ε)) * W (a + ε) ≤
          Real.exp (-φ * (a + ε)) * W a :=
      mul_le_mul_of_nonneg_left hWle (Real.exp_pos _).le
    have hmul2 :
        Real.exp (-φ * (a + ε)) * W a <
          Real.exp (-φ * a) * W a :=
      mul_lt_mul_of_pos_right hexp (hposW a ha)
    exact (not_lt_of_ge hmono') (lt_of_le_of_lt hmul1 hmul2)
  obtain ⟨w, hw, hbudget, hstep⟩ :=
    stoppedFirstRecord_upper_geometric_budgets
      X hX q hq W hW a ε ha hε hWright hWa hWinc
  apply barrierSupValue_le_right_scale_quotient_of_killed_grid_step
    X W a 0 q ε hq.le hε hWright hWa hWinc w
  · intro n ω
    simpa only [zero_add] using hw n ω
  · exact hbudget
  · exact hstep
