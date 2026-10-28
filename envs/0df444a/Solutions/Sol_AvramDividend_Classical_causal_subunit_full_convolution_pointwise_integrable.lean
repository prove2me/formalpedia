-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_full_convolution_pointwise_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:20:40.371114+00:00
-- url     : https://prove2.me/submissions/cc98b0d1-45f1-46ca-b81c-bc1472a81773

import Theorems.Thm_AvramDividend_Classical_causal_subunit_any_real_recursion_power_bounds
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_antitone_L1_split_product_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_reflected_interval_to_global_convolution_integrable
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set


theorem solution
    (k : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hanti : AntitoneOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hkpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ k t)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => k y * F n (x - y)) volume  := by 
  obtain ⟨-, hFi, hFp, hFb⟩ := causal_subunit_any_real_recursion_power_bounds k ρ F hρpos hρlt hcont
    hanti hkzero hkpos hkL1 hmass hFzero hFsucc
  have hz := causal_full_convolution_powers_zero_nonpositive k F hkzero hFzero hFsucc
  intro n x
  rcases le_or_gt x 0 with hx | hx
  · have : (fun y : ℝ => k y * F n (x - y)) = fun _ => 0 := by
      funext y
      rcases le_or_gt y 0 with hy | hy
      · rw [hkzero y hy, zero_mul]
      · rw [hz n (x - y) (by linarith), mul_zero]
    rw [this]; exact integrable_zero _ _ _
  · refine causal_reflected_interval_to_global_convolution_integrable k (F n) x hx.le hkzero (hz n) ?_
    exact causal_antitone_L1_split_product_intervalIntegrable k (F n) x ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) hx
      (by positivity) hanti hcont (fun t ht => hkpos t ht.le) hkL1 (fun s hs => hFp n s hs.le)
      (fun s hs => hFb n s hs) (hFi n)
