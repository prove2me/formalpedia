-- Prove2me | solution 2 for AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:30:14.148723+00:00
-- url     : https://prove2.me/submissions/60d6b9a9-83e6-4a14-b9b8-ebfc42ac5a22

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_interval_integrable_at_zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Subunit causal convolution powers form a renewal density integrable at zero. -/
theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x) := by
  obtain ⟨_, F, hFzero, hFrec, hFi, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hFnzero :=
    causal_full_convolution_powers_zero_nonpositive κ F hκzero hFzero hFrec
  have hmassgeo :=
    causal_full_convolution_powers_exact_geometric_mass
      κ F hκzero hκL1 hFzero hFrec hFi
  have hsum (x : ℝ) (hx : 0 < x) :
      Summable (fun n : ℕ => F n x) :=
    renewal_density_series_summable_of_geometric_power_bound
      ρ x (le_of_lt hρpos) hρlt hx (fun n => F n x)
      (fun n => hFpos n x (le_of_lt hx))
      (fun n => hFbound n x hx)
  have hgeo (n : ℕ) :
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) ≤ ρ ^ (n + 1) := by
    rw [hmassgeo n, hmass]
  refine ⟨F, hFzero, hFrec, hFi, hFpos, hFbound, ?_⟩
  exact causal_geometric_renewal_interval_integrable_at_zero
    F ρ (le_of_lt hρpos) hρlt hFi hFnzero
    (fun n x hx => hFpos n x (le_of_lt hx)) hsum hgeo
