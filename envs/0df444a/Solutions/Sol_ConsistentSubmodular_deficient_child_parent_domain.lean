-- Prove2me | solution 1 for ConsistentSubmodular.deficient_child_parent_domain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:28.977991+00:00
-- url     : https://prove2.me/submissions/32ccd1ae-5a28-477b-b9a0-577437a22f17

import Mathlib

section

namespace ConsistentSubmodular

theorem relay_baseline_upgrade_identity (d₀ e W b k : ℝ)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    (3 - k) * (b + W + e - 3 * (d₀ + e)) =
      (4 - k) * b - (2 - k) * (3 * d₀ + 3 * e) := by
  nlinarith only [hatt]

theorem relay_baseline_upgrade_high (d₀ e W b k : ℝ)
    (hd : 0 ≤ d₀) (he : 0 ≤ e) (hb : 0 ≤ b) (hk2 : 2 ≤ k) (hk3 : k < 3)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    3 * (d₀ + e) ≤ b + W + e := by
  have h1 := mul_nonneg (show 0 ≤ 4 - k by linarith) hb
  have h2 := mul_nonneg (show 0 ≤ k - 2 by linarith) (show 0 ≤ 3 * d₀ + 3 * e by positivity)
  have hid := relay_baseline_upgrade_identity d₀ e W b k hatt
  have hprod : 0 ≤ (3 - k) * (b + W + e - 3 * (d₀ + e)) := by nlinarith only [hid, h1, h2]
  have := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  linarith

theorem relay_baseline_upgrade_budget (d₀ e W b L k : ℝ)
    (hchild : d₀ + e ≤ 1 / 4) (hLb : L ≤ b) (_hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hbudget : (3 : ℝ) / 4 * (2 - k) ≤ (4 - k) * L)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    3 * (d₀ + e) ≤ b + W + e := by
  have h1 := mul_nonneg (show 0 ≤ 4 - k by linarith) (sub_nonneg.mpr hLb)
  have h2 := mul_nonneg (sub_nonneg.mpr hk2) (show 0 ≤ 3 / 4 - (3 * d₀ + 3 * e) by linarith)
  have hid := relay_baseline_upgrade_identity d₀ e W b k hatt
  have hprod : 0 ≤ (3 - k) * (b + W + e - 3 * (d₀ + e)) := by
    nlinarith only [hid, h1, h2, hbudget]
  have := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  linarith

theorem relay_baseline_upgrade_quarter (d₀ e W b L k : ℝ)
    (hd : 0 ≤ d₀) (he : 0 ≤ e) (hchild : d₀ + e ≤ 1 / 4)
    (hL : (1 : ℝ) / 4 ≤ L) (hLb : L ≤ b) (hk1 : 1 ≤ k) (hk3 : k < 3)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    3 * (d₀ + e) ≤ b + W + e := by
  by_cases hk2 : 2 ≤ k
  · exact relay_baseline_upgrade_high d₀ e W b k hd he (by linarith) hk2 hk3 hatt
  · apply relay_baseline_upgrade_budget d₀ e W b L k hchild hLb hk1
      (le_of_not_ge hk2) ?_ hatt
    have := mul_nonneg (show 0 ≤ 4 - k by linarith) (sub_nonneg.mpr hL)
    nlinarith

theorem high_parent_small_parameter_polynomial (k d₀ : ℝ)
    (_hk1 : 1 ≤ k) (hk4 : k ≤ (4 : ℝ) / 3) (hd : d₀ ≤ 1 / 8) :
    0 ≤ (2 - 4 * d₀) * k ^ 2 + (29 * d₀ - 9) * k + 9 - 36 * d₀ := by
  have hcoef : -4 * k ^ 2 + 29 * k - 36 ≤ 0 := by nlinarith [sq_nonneg (k - 1)]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd) hcoef
  have h2 := mul_nonneg_of_nonpos_of_nonpos (show 3 * k - 4 ≤ 0 by linarith)
    (show 4 * k - 9 ≤ 0 by linarith)
  nlinarith only [h1, h2]

/-- High parents cannot have a failed attaining-credit test below four thirds. -/
theorem high_parent_small_parameter_credit (k d₀ e W b : ℝ)
    (hk1 : 1 ≤ k) (hk4 : k ≤ (4 : ℝ) / 3) (hd : d₀ ≤ 1 / 8)
    (he : 0 ≤ e) (hb : 2 * d₀ ≤ b)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    2 * (1 - d₀) * k - 3 * (1 - 4 * d₀) ≤ k * (b + W) := by
  have hF := high_parent_small_parameter_polynomial k d₀ hk1 hk4 hd
  have h1 := mul_nonneg (mul_nonneg (show 0 ≤ k by linarith)
    (show 0 ≤ 4 - k by linarith)) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg (sq_nonneg k) he
  have hrel := congrArg (fun x : ℝ => k * x) hatt
  have hprod : 0 ≤ (3 - k) *
      (k * (b + W) - (2 * (1 - d₀) * k - 3 * (1 - 4 * d₀))) := by
    nlinarith only [hF, h1, h2, hrel]
  have := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  linarith

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (d₀ e W b L k : ℝ)
    (hd : 0 ≤ d₀) (he : 0 ≤ e) (hchild : d₀ + e ≤ 1 / 4)
    (hL : 2 * d₀ ≤ L) (hLb : L ≤ b) (hk1 : 1 ≤ k) (hk3 : k < 3)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀)
    (hdeficient : b + W + e < 3 * (d₀ + e))
    (hfailed : k * (b + W) < 2 * (1 - d₀) * k - 3 * (1 - 4 * d₀)) :
    (4 : ℝ) / 3 < k ∧ k < 2 ∧ d₀ < 1 / 8 := by
  have hk2 : k < 2 := by
    by_contra hn
    have := relay_baseline_upgrade_high d₀ e W b k hd he (by linarith)
      (le_of_not_gt hn) hk3 hatt
    linarith
  have hL4 : L < 1 / 4 := by
    by_contra hn
    have := relay_baseline_upgrade_quarter d₀ e W b L k hd he hchild
      (le_of_not_gt hn) hLb hk1 hk3 hatt
    linarith
  have hd8 : d₀ < 1 / 8 := by linarith
  refine ⟨?_, hk2, hd8⟩
  by_contra hn
  have := high_parent_small_parameter_credit k d₀ e W b hk1 (le_of_not_gt hn)
    hd8.le he (hL.trans hLb) hatt
  linarith

end
