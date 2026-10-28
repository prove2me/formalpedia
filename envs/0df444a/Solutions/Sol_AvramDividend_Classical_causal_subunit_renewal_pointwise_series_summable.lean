-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_pointwise_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:22:06.507667+00:00
-- url     : https://prove2.me/submissions/c42dc652-4a7c-4735-b97e-9b19c1026cb0

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ t : ℝ, t ≤ 0 → κ t = 0)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s : ℝ, κ s * F n (x - s) ∂volume) ∧
      (∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x)) := by
  obtain ⟨-, F, h0, hrec, -, hnn, hb⟩ :=
    AvramDividend.Classical.causal_subunit_renewal_full_real_power_package κ ρ hρpos hρone
      hcont hanti hκzero hκpos hκL1 hmass
  exact ⟨F, h0, hrec, fun x hx =>
    AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound ρ x
      hρpos.le hρone hx (fun n => F n x) (fun n => hnn n x hx.le) (fun n => hb n x hx)⟩
