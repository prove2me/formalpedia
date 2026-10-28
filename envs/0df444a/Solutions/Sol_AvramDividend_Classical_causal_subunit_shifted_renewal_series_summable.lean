-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_shifted_renewal_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:46:28.689719+00:00
-- url     : https://prove2.me/submissions/4ea4b134-606c-434a-8f13-d4299bb27d63

import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Every causal subunit convolution-power series, including its shifted form, converges pointwise. -/
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
      if n = 0 then (0 : ℝ) else F (n - 1) x) := by
  have hFnzero :=
    causal_full_convolution_powers_zero_nonpositive
      k F hkzero hFzero hFsucc
  intro x
  have hseries : Summable (fun n : ℕ => F n x) := by
    by_cases hx : 0 < x
    · exact renewal_density_series_summable_of_geometric_power_bound
        ρ x (le_of_lt hρpos) hρlt hx (fun n => F n x)
        (fun n => hFpos n x (le_of_lt hx))
        (fun n => hFbound n x hx)
    · have hz : (fun n : ℕ => F n x) =
        (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        exact hFnzero n x (le_of_not_gt hx)
      rw [hz]
      exact summable_zero
  let g : ℕ → ℝ := fun n =>
    if n = 0 then 0 else F (n - 1) x
  have htail : (fun n : ℕ => g (n + 1)) =
      (fun n : ℕ => F n x) := by
    funext n
    simp [g]
  have hg : Summable g := by
    apply (summable_nat_add_iff 1).mp
    simpa only [htail] using hseries
  exact hg
