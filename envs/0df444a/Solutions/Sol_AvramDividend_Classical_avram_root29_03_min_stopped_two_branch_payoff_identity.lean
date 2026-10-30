-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_min_stopped_two_branch_payoff_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:55:51.366266+00:00
-- url     : https://prove2.me/submissions/fc7f204f-b800-489a-9c65-f794b75cdeb2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_finite_reward_split
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_lower_stopped_payoff_at_min_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual finite stopped-minimum reward is exactly the sum of its
strict upper-first and lower-first branch rewards, with no assumption
about lower creeping or killed-scale harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a)
    (g : ℝ≥0∞ → Ω → ℝ≥0∞)
    (hg : Measurable (fun ω => g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω)) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      g (twoSidedExitUpTime X (a - x) ω) ω else 0 ∂μ) +
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
      g (twoSidedExitDownTime X (-x) ω) ω else 0 ∂μ) := by
  have hUpper :
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) =
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        g (twoSidedExitUpTime X (a - x) ω) ω else 0 ∂μ) := by
    refine lintegral_congr fun ω => ?_
    by_cases hu : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
    · have hMin : min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) = twoSidedExitUpTime X (a - x) ω :=
        min_eq_left (le_of_lt hu)
      simp [hu, hMin]
    · simp [hu]
  have hLower :
      (∫⁻ ω, if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) =
      (∫⁻ ω, if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        g (twoSidedExitDownTime X (-x) ω) ω else 0 ∂μ) :=
    avram_root29_03_lower_stopped_payoff_at_min_clock X a x g
  calc
    _ = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < ⊤ ∨ twoSidedExitDownTime X (-x) ω < ⊤ then
        g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) := by
      refine lintegral_congr fun ω => ?_
      simp only [min_lt_iff]
    _ = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
          g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) +
        (∫⁻ ω, if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
          g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) :=
      avram_root29_03_exit_finite_reward_split
        X a x ha (fun ω => g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω) hg
    _ = _ := congrArg₂ (· + ·) hUpper hLower
