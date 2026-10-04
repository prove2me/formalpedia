-- Prove2me | solution 1 for AvramDividend.Classical.discounted_jump_compensator_lintegral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T23:10:20.081295+00:00
-- url     : https://prove2.me/submissions/144e6336-c956-4c07-b084-0b968c7350f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_discounted_jump_compensator_bound

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ≥0)
    (hμ : (∫⁻ z : ℝ≥0,
       ENNReal.ofReal (min (z : ℝ) 1) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
            ((n : ℝ) + 1)) ∂μ)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  let F : ℕ → ℝ≥0 → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal
      ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1))
  let B : ℝ≥0 → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (min (z : ℝ) 1)
  have hreal (n : ℕ) (z : ℝ≥0) :
      0 ≤ (1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1) ∧
      (1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1) ≤ min (z : ℝ) 1 := by
    apply discounted_jump_compensator_bound
    · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact NNReal.coe_nonneg z
  have hmeas : ∀ n : ℕ, Measurable (F n) := by
    intro n
    dsimp [F]
    fun_prop
  have hmajor : ∀ n : ℕ, F n ≤ᵐ[μ] B := by
    intro n
    apply Filter.Eventually.of_forall
    intro z
    exact ENNReal.ofReal_le_ofReal (hreal n z).2
  have hpoint (z : ℝ≥0) :
      Tendsto (fun n : ℕ => F n z) Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hreal0 : Tendsto
        (fun n : ℕ =>
          (1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 (0 : ℝ)) := by
      have hupper (n : ℕ) :
          (1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
        have hden : 0 ≤ (n : ℝ) + 1 := by positivity
        have hexp : 0 < Real.exp (-((n : ℝ) + 1) * (z : ℝ)) :=
          Real.exp_pos _
        have hnum : 1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ)) ≤ 1 := by
          linarith
        exact div_le_div_of_nonneg_right hnum hden
      exact squeeze_zero (fun n => (hreal n z).1)
        hupper tendsto_one_div_add_atTop_nhds_zero_nat
    have hf := ENNReal.tendsto_ofReal hreal0
    simpa only [F, ENNReal.ofReal_zero] using hf
  have hae : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ => F n z)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Eventually.of_forall hpoint
  have hdct := tendsto_lintegral_of_dominated_convergence
    B hmeas hmajor hμ hae
  simpa [F, B] using hdct
