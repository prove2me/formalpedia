-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_left_step_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:32:49.142027+00:00
-- url     : https://prove2.me/submissions/1c91bbc4-c2e0-4063-8950-d9cda31653b5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_actual_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine killed reflected reward dominates its left finite-difference
scale quotient at every positive mesh strictly below the barrier, without C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by
  obtain ⟨hposW, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hleftpos : 0 < a - ε := by linarith
  have hWa : 0 < W a := hposW a ha
  have hWleftpos : 0 < W (a - ε) := hposW (a - ε) hleftpos
  have hWleft : 0 ≤ W (a - ε) := hWleftpos.le
  have hmono' :
      Real.exp (-φ * (a - ε)) * W (a - ε) ≤
        Real.exp (-φ * a) * W a := by
    exact hmono (Set.mem_Ioi.mpr hleftpos)
      (Set.mem_Ioi.mpr ha) (by linarith)
  have hexp :
      Real.exp (-φ * a) < Real.exp (-φ * (a - ε)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos hφ hε]
  have hWinc : W (a - ε) < W a := by
    by_contra hnot
    have hWle : W a ≤ W (a - ε) := le_of_not_gt hnot
    have hmul1 :
        Real.exp (-φ * a) * W a ≤
          Real.exp (-φ * a) * W (a - ε) :=
      mul_le_mul_of_nonneg_left hWle (Real.exp_pos _).le
    have hmul2 :
        Real.exp (-φ * a) * W (a - ε) <
          Real.exp (-φ * (a - ε)) * W (a - ε) :=
      mul_lt_mul_of_pos_right hexp hWleftpos
    exact (not_lt_of_ge hmono') (lt_of_le_of_lt hmul1 hmul2)
  have hx0 : 0 ≤ a - ε := by linarith
  have hxa : a - ε ≤ a := by linarith
  have hcore :=
    two_sided_exit_before_ruin_integral_identity X hX q hq W hW
      a (a - ε) ha hx0 hxa
  have hu : a - (a - ε) = ε := by ring
  have hl : -(a - ε) = ε - a := by ring
  have hExit :
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a) := by
    simpa only [hu, hl] using hcore
  apply barrierSupValue_ge_left_scale_quotient_of_actual_grid
    X W a q ε hq.le hε hWa hWleft hWinc
  exact killed_firstRecord_grid_expected_scale_lower_of_strict_exit
    X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc hExit
