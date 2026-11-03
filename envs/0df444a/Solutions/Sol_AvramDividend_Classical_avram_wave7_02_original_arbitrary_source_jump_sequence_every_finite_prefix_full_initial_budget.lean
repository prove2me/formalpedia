-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:11:59.945528+00:00
-- url     : https://prove2.me/submissions/631df2d1-e1fc-4a1e-962c-1e3a579c4399

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- All finite prefixes of actual original pre-ruin source/payments satisfy
the exact initial Stieltjes budget without any summability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hTimes : ∀ n, 0 < t n ∧ (t n : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ n,
      X.X (t n) ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω) ≤ C) :
    let J : ℕ → ℝ := fun i =>
      Real.exp (-(q * (t i : ℝ))) *
        ((w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω))
    ∀ n : ℕ, (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n, J i) ≤ w x := by
  dsimp only
  intro n
  have hZero :=
    (avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
      X x D hD w hjump ω).1
  have hEach : ∀ i : ℕ,
      Real.exp (-(q * (t i : ℝ))) *
        ((w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω)) ≤ 0 := by
    intro i
    obtain ⟨hPos, hPre⟩ := hTimes i
    obtain ⟨hMark, hBase, hCap⟩ := hValid i
    have hDrop :=
      avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
        X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
        x D ω (t i) hMark hBase hCap
    have hPayment :=
      (avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
        X x D w hjump ω (t i) hPos hPre).1
    have hCombined :
        (w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω) ≤ 0 := by
      linarith only [hDrop, hPayment]
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) hCombined
  have hPrefix := Finset.sum_nonpos (s := Finset.range n) (fun i hi => hEach i)
  linarith only [hZero, hPrefix]
