-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exact_qscale_two_branch_terminal_conversion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:06:54.67999+00:00
-- url     : https://prove2.me/submissions/40da80dc-7358-41e7-9bbc-06096b2d4735

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_two_branch_payoff_identity
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_qscale_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_terminal_payoff_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual q-scale terminal reward at the finite first two-sided exit
equals exactly the sum of the strict upper and lower stopped q-scale
terminal payoffs in the source be9 harmonicity statement. This
conversion contains no killed stochastic identity or creeping premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0) +
      (if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω)) else 0) ∂P) := by
  let g : ℝ≥0∞ → Ω → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal t))) *
      ENNReal.ofReal (W (x + X.X t.toNNReal ω))
  have hg : Measurable (fun ω : Ω => g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω) :=
    avram_root29_03_min_stopped_qscale_reward_measurable X q W hW a x
  have hSplit := avram_root29_03_min_stopped_two_branch_payoff_identity
    (μ := P) X a x ha g hg
  have hUpper :
      Measurable (fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
        else 0) :=
    chat04_strict_upper_exit_scale_terminal_payoff_measurable
      X q a x hxa W
  rw [← lintegral_add_left hUpper] at hSplit
  simpa only [g] using hSplit
