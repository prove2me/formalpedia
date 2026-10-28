-- Prove2me | solution 2 for AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:50:27.477159+00:00
-- url     : https://prove2.me/submissions/7784509e-70e1-4adb-bfdf-2602d029173c

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_causal_shifted_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (κ : ℝ → ℝ) (ρ b : ℝ)
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
      ContinuousOn
        (fun x : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y)
          volume 0 x) := by
  obtain ⟨F, h0, hrec, -, hpos, hbd, hI⟩ :=
    AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero κ ρ hρpos
      hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hκb : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := fun ε hε =>
    ⟨κ ε, fun x hx => by
      rw [abs_of_nonneg (hκpos x (hε.le.trans hx))]
      exact hanti (mem_Ioi.2 hε) (mem_Ioi.2 (hε.trans_le hx)) hx⟩
  refine ⟨F, h0, hrec, ?_, ?_⟩
  · exact AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds κ F ρ hρpos
      hρlt (AvramDividend.Classical.causal_positive_l1_global_integrable κ hκL1 hκzero) hcont hκzero
      hκb h0 hrec hpos hbd
  · exact AvramDividend.Classical.causal_shifted_renewal_density_interval_integrable_at_zero F b
      (fun y hy => AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound ρ y
        hρpos.le hρlt hy _ (fun n => hpos n y hy.le) (fun n => hbd n y hy)) hI
