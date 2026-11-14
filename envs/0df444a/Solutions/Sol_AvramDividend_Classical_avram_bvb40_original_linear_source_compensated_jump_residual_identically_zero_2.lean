-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:21:40.663654+00:00
-- url     : https://prove2.me/submissions/8533ca47-fd2b-4ab8-9820-0d0f5f796daf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift)
    (t : ℝ≥0) (ht : t ≤ S) :
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0  := by
  have hEach (v : ℝ≥0) :
      (if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
       else 0) = 0 := by
    split_ifs with hv
    · have hJump :=
        avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
          X ω S hSource v (hv.2.trans ht)
      linarith
    · rfl
  have hSum : (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0) = 0 := by
    simp only [hEach, tsum_zero]
  rw [hSource t ht, hSum]
  ring
