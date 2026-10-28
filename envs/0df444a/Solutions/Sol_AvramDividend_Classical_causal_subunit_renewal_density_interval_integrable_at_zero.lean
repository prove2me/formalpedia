-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:29:56.938601+00:00
-- url     : https://prove2.me/submissions/3d613504-fa98-414a-bde2-d1077e45f3f3

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_interval_integrable_at_zero

open AvramDividend.Classical MeasureTheory Set

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
  obtain ⟨-, F, h0, hrec, hint, hpos, hbd⟩ :=
    AvramDividend.Classical.causal_subunit_renewal_full_real_power_package κ ρ hρpos hρlt hcont
      hanti hκzero hκpos hκL1 hmass
  refine ⟨F, h0, hrec, hint, hpos, hbd, ?_⟩
  refine AvramDividend.Classical.causal_geometric_renewal_interval_integrable_at_zero F ρ hρpos.le hρlt
    hint (AvramDividend.Classical.causal_full_convolution_powers_zero_nonpositive κ F hκzero h0 hrec)
    (fun n x hx => hpos n x hx.le)
    (fun x hx => AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound ρ x
      hρpos.le hρlt hx _ (fun n => hpos n x hx.le) (fun n => hbd n x hx))
    (fun n => ?_)
  rw [AvramDividend.Classical.causal_full_convolution_powers_exact_geometric_mass κ F hκzero hκL1 h0
    hrec hint n, hmass]
