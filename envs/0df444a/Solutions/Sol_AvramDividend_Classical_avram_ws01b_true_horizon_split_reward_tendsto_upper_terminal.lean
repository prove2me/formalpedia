-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:21:20.581998+00:00
-- url     : https://prove2.me/submissions/2d873dad-2795-4828-8034-1a34862e8c95

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_discounted_scale_decay
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- As natural horizons grow, actual killed reward components converge to the true upper payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) :
    Tendsto (fun n : ℕ =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ (n : ℝ≥0) then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if ((n : ℝ≥0) : ℝ≥0∞) < U ∧ ((n : ℝ≥0) : ℝ≥0∞) < D then
        Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
      else 0)) atTop
      (𝓝 (if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0)) := by
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  change Tendsto (fun n : ℕ =>
      (if U < D ∧ U.toNNReal ≤ (n : ℝ≥0) then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if ((n : ℝ≥0) : ℝ≥0∞) < U ∧ ((n : ℝ≥0) : ℝ≥0∞) < D then
        Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
      else 0)) atTop
      (𝓝 (if U < D then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0))
  rcases lt_trichotomy U D with hUp | hEq | hDown
  · have hUfin : U < ⊤ := lt_of_lt_of_le hUp le_top
    have hCoe : (U.toNNReal : ℝ≥0∞) = U :=
      ENNReal.coe_toNNReal (ne_of_lt hUfin)
    have hEvent : ∀ᶠ n : ℕ in atTop, U.toNNReal ≤ (n : ℝ≥0) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨Nat.ceil U.toNNReal, ?_⟩
      intro n hn
      calc
        U.toNNReal ≤ (Nat.ceil U.toNNReal : ℝ≥0) := Nat.le_ceil _
        _ ≤ (n : ℝ≥0) := by exact_mod_cast hn
    apply tendsto_const_nhds.congr'
    filter_upwards [hEvent] with n hn
    have hUn : U ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
      rw [← hCoe]
      exact ENNReal.coe_le_coe.mpr hn
    have hNotSurv : ¬ (((n : ℝ≥0) : ℝ≥0∞) < U ∧
          ((n : ℝ≥0) : ℝ≥0∞) < D) := by
      intro hh
      exact (not_lt.mpr hUn) hh.1
    have hCast : (((n : ℝ≥0) : ℝ≥0∞)) = (n : ℝ≥0∞) := by
      norm_cast
    have hNotSurv' : ¬ ((n : ℝ≥0∞) < U ∧ (n : ℝ≥0∞) < D) := by
      simpa only [hCast] using hNotSurv
    simp [hUp, hn, hNotSurv']
  · have hUinf : U = ⊤ :=
      chat04_two_sided_strict_exit_no_finite_tie X a x ha hxa ω hEq
    have hDinf : D = ⊤ := hEq.symm.trans hUinf
    have hDecay := avram_ws01b_true_never_exit_discounted_scale_decay
      X q hq W hW a x ha hx0 hxa ω hUinf hDinf
    simpa [hUinf, hDinf] using hDecay
  · have hDfin : D < ⊤ := lt_of_lt_of_le hDown le_top
    have hCoe : (D.toNNReal : ℝ≥0∞) = D :=
      ENNReal.coe_toNNReal (ne_of_lt hDfin)
    have hEvent : ∀ᶠ n : ℕ in atTop, D.toNNReal ≤ (n : ℝ≥0) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨Nat.ceil D.toNNReal, ?_⟩
      intro n hn
      calc
        D.toNNReal ≤ (Nat.ceil D.toNNReal : ℝ≥0) := Nat.le_ceil _
        _ ≤ (n : ℝ≥0) := by exact_mod_cast hn
    apply tendsto_const_nhds.congr'
    filter_upwards [hEvent] with n hn
    have hDn : D ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
      rw [← hCoe]
      exact ENNReal.coe_le_coe.mpr hn
    have hNotUp : ¬ U < D := not_lt_of_ge hDown.le
    have hNotSurv : ¬ (((n : ℝ≥0) : ℝ≥0∞) < U ∧
          ((n : ℝ≥0) : ℝ≥0∞) < D) := by
      intro hh
      exact (not_lt.mpr hDn) hh.2
    have hCast : (((n : ℝ≥0) : ℝ≥0∞)) = (n : ℝ≥0∞) := by
      norm_cast
    have hNotSurv' : ¬ ((n : ℝ≥0∞) < U ∧ (n : ℝ≥0∞) < D) := by
      simpa only [hCast] using hNotSurv
    simp [hNotUp, hNotSurv']
