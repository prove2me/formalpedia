-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_reflected_pair_killed_scale_monotone_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:11:59.981882+00:00
-- url     : https://prove2.me/submissions/9ac70359-51e4-492d-927f-823fa7753160

import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- Monotonicity in initial reserve of the genuine reflected-pair killed
    scale reward. The actual joint law is used, with no WH factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x₁ x₂ : ℝ) (hxx : x₁ ≤ x₂) :
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x₁ then ENNReal.ofReal (W (x₁ - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) ≤
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x₂ then ENNReal.ofReal (W (x₂ - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by
  have hPair₁ :=
    chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
      P X r hr x₁ q W hW
  have hPair₂ :=
    chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
      P X r hr x₂ q W hW
  rw [← hPair₁, ← hPair₂]
  have hmon : MonotoneOn W (Ici 0) := hW.2.2.2.1
  apply lintegral_mono
  intro z
  by_cases h₁ : ∀ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 → 0 ≤ x₁ + X.X s z.1
  · have h₂ : ∀ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 → 0 ≤ x₂ + X.X s z.1 := by
      intro s hs
      have h := h₁ s hs
      linarith
    simp only [if_pos h₁, if_pos h₂]
    apply ENNReal.ofReal_le_ofReal
    have hstart : 0 ≤ x₁ + X.X (Real.toNNReal z.2) z.1 :=
      h₁ _ le_rfl
    have hend : 0 ≤ x₂ + X.X (Real.toNNReal z.2) z.1 :=
      h₂ _ le_rfl
    exact hmon hstart hend (by linarith)
  · simp only [if_neg h₁]
    exact bot_le

