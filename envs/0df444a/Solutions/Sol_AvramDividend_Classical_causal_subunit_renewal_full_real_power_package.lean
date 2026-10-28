-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_full_real_power_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:34:33.689987+00:00
-- url     : https://prove2.me/submissions/812efcb0-d2ca-4b97-a941-8425f6b22358

import Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_subunit_convolution_powers
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Assemble a causal subunit renewal kernel's globally integrable
real convolution-power package, with the exact full-line recurrence. -/
theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ t : ℝ, t ≤ 0 → κ t = 0)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    Integrable κ volume ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s : ℝ, κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 < x →
          F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by
  have hglob : Integrable κ volume :=
    causal_positive_l1_global_integrable κ hκL1 hκzero
  obtain ⟨F, hF0, hFsucc, hFL1, hFpos, hFbound⟩ :=
    causal_continuous_antitone_subunit_convolution_powers
      κ ρ hρpos hρone hcont hanti hκpos hκL1 hmass
  obtain ⟨_, hfull⟩ :=
    causal_Ioc_convolution_powers_full_real_recursion
      κ F hκzero hF0 hFsucc
  exact ⟨hglob, F, hF0, hfull, hFL1, hFpos, hFbound⟩
