-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_never_exit_discounted_scale_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:38:51.456416+00:00
-- url     : https://prove2.me/submissions/3d2f4371-0e96-4bdc-bdae-ad50afd6b286

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_scale_strip_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- The original Lévy stopped reward vanishes at infinite horizon on never-exiting paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a-x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
      atTop (𝓝 0) := by
  have hWbound := avram_ws01b_true_never_exit_scale_strip_bound
    X q W hW a x ha hx0 hxa ω hUp hDown
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hExpRight : Tendsto
      (fun n : ℕ => Real.exp (-((n : ℝ) * q))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hNat.atTop_mul_const hq)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-(q * (n : ℝ))))
      atTop (𝓝 0) := by
    have heq : (fun n : ℕ => Real.exp (-(q * (n : ℝ)))) =
        (fun n : ℕ => Real.exp (-((n : ℝ) * q))) := by
      funext n
      rw [mul_comm q]
    rw [heq]
    exact hExpRight
  have hUpper : Tendsto
      (fun n : ℕ => Real.exp (-(q * (n : ℝ))) * W a)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hExp.mul_const (W a)
  apply Filter.Tendsto.squeeze tendsto_const_nhds hUpper
  · intro n
    exact mul_nonneg (Real.exp_nonneg _) (hWbound (n : ℝ≥0)).1
  · intro n
    exact mul_le_mul_of_nonneg_left
      (hWbound (n : ℝ≥0)).2 (le_of_lt (Real.exp_pos _))
