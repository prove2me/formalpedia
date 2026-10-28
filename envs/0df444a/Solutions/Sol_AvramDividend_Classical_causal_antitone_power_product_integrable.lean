-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_power_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:26:02.002967+00:00
-- url     : https://prove2.me/submissions/52be37b9-dc30-4a4c-a3e9-9634f764007a

import Theorems.Thm_AvramDividend_Classical_causal_antitone_L1_split_product_intervalIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- All envelope convolution products are integrable from their L1 and 1/x bounds. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ n : ℕ, ∀ s : ℝ, 0 < s → 0 ≤ F n s)
    (hFpoint : ∀ n : ℕ, ∀ s : ℝ, 0 < s →
      F n s ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / s) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x := by
  intro n x hx
  exact causal_antitone_L1_split_product_intervalIntegrable
    κ (F n) x (((n + 1 : ℝ) ^ 2) * ρ ^ (n + 1)) hx
    (mul_nonneg (sq_nonneg _) (pow_nonneg hρ0 _))
    hκanti hκcont hκnonneg hκL1
    (hFnonneg n) (hFpoint n) (hFL1 n)
