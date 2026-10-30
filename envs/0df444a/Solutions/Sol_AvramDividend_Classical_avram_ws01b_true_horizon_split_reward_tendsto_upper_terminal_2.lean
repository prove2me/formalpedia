-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:21:25.057424+00:00
-- url     : https://prove2.me/submissions/177ee985-8b82-43c6-891c-f6506e75e001

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_discounted_scale_decay

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

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
  have hev : ∀ c : ℝ≥0, ∀ᶠ n : ℕ in atTop, c < (n : ℝ≥0) :=
    fun c => (tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_gt_atTop c
  dsimp only
  generalize hU : twoSidedExitUpTime X (a-x) ω = U
  generalize hD : twoSidedExitDownTime X (-x) ω = D
  induction U using ENNReal.recTopCoe <;> induction D using ENNReal.recTopCoe
  · simpa using avram_ws01b_true_never_exit_discounted_scale_decay X q hq W hW a x ha hx0 hxa ω hU hD
  · rename_i d
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev d] with n hn
    simp [not_lt.mpr hn.le]
    intro h; exact absurd h (by exact_mod_cast not_lt.mpr hn.le)
  · rename_i u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev u] with n hn
    simp [hn.le, not_lt.mpr hn.le]
  · rename_i u d
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev u, hev d] with n hn1 hn2
    have a1 : ¬ (((n:ℝ≥0):ℝ≥0∞) < (u:ℝ≥0∞)) := by exact_mod_cast not_lt.mpr hn1.le
    have b1 : ((u:ℝ≥0∞)).toNNReal ≤ (n:ℝ≥0) := by simpa using hn1.le
    by_cases h : (u:ℝ≥0∞) < d
    · rw [if_pos h, if_pos ⟨h, b1⟩, if_neg (not_and_of_not_left _ a1), add_zero]
    · rw [if_neg h, if_neg (fun hh => h hh.1), if_neg (not_and_of_not_left _ a1), add_zero]
