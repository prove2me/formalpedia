-- Prove2me | solution 2 for AvramDividend.Classical.causal_subunit_shifted_renewal_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:47:44.13673+00:00
-- url     : https://prove2.me/submissions/aef1dba6-c2c9-4bb1-a48c-6a053d545f30

import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open AvramDividend.Classical MeasureTheory Set


theorem solution
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      if n = 0 then (0 : ℝ) else F (n - 1) x)  := by 
  intro x
  rw [← summable_nat_add_iff 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  rcases le_or_gt x 0 with hx | hx
  · have h0 := causal_full_convolution_powers_zero_nonpositive k F hkzero hFzero hFsucc
    simp only [h0 _ x hx]
    exact summable_zero
  · exact renewal_density_series_summable_of_geometric_power_bound ρ x hρpos.le hρlt hx
      (fun n => F n x) (fun n => hFpos n x hx.le) (fun n => hFbound n x hx)
