-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:54:33.387496+00:00
-- url     : https://prove2.me/submissions/4f4a2177-788c-4d04-a227-3c3c0b0f0539

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
import Mathlib.Analysis.SpecificLimits.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Subunit renewal resolvents have an L1 density with exact geometric total mass. -/
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
      IntegrableOn (fun x : ℝ => ∑' n : ℕ, F n x)
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x ∂volume) =
        ρ / (1 - ρ) := by
  obtain ⟨_, F, hFzero, hFrec, hFi, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hFnzero :=
    causal_full_convolution_powers_zero_nonpositive κ F hκzero hFzero hFrec
  have hgeo :=
    causal_full_convolution_powers_exact_geometric_mass
      κ F hκzero hκL1 hFzero hFrec hFi
  have hmasses (n : ℕ) :
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) = ρ ^ (n + 1) := by
    rw [hgeo n, hmass]
  have hposAll (n : ℕ) (x : ℝ) : 0 ≤ F n x := by
    by_cases hx : 0 < x
    · exact hFpos n x (le_of_lt hx)
    · rw [hFnzero n x (le_of_not_gt hx)]
  have hmasssum :
      Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), F n x ∂volume) := by
    simp_rw [hmasses]
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one (le_of_lt hρpos) hρlt).mul_left ρ
  have hpoint (x : ℝ) : Summable (fun n : ℕ => F n x) := by
    by_cases hx : 0 < x
    · exact renewal_density_series_summable_of_geometric_power_bound
        ρ x (le_of_lt hρpos) hρlt hx (fun n => F n x)
        (fun n => hFpos n x (le_of_lt hx))
        (fun n => hFbound n x hx)
    · have hz : (fun n : ℕ => F n x) = (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        exact hFnzero n x (le_of_not_gt hx)
      rw [hz]
      exact summable_zero
  have hL1 := nonnegative_integrable_tsum_of_summable_integrals
    (volume.restrict (Ioi (0 : ℝ))) F hFi hposAll
    hpoint hmasssum
  have hexchange :=
    nonnegative_renewal_integral_tsum_exchange
      (volume.restrict (Ioi (0 : ℝ))) F hFi hposAll hmasssum
  refine ⟨F, hFzero, hFrec, hFi, hL1, ?_⟩
  calc
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x ∂volume) =
      ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), F n x ∂volume := hexchange
    _ = ρ / (1 - ρ) :=
      causal_geometric_renewal_total_mass_sum F ρ
        (le_of_lt hρpos) hρlt hmasses