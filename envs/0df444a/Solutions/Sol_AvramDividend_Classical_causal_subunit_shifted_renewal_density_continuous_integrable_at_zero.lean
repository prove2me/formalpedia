-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:50:00.032536+00:00
-- url     : https://prove2.me/submissions/c469ecd1-c033-4974-a382-e99f11437991

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_causal_shifted_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A subunit causal renewal kernel has a continuous, scaled density integrable from zero. -/
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
  obtain ⟨F, hFzero, hFrec, _hFi, hFpos, hFbound, hInt⟩ :=
    causal_subunit_renewal_density_interval_integrable_at_zero
      κ ρ hρpos hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hκglob : Integrable κ volume :=
    causal_positive_l1_global_integrable κ hκL1 hκzero
  have hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    rw [abs_of_nonneg (hκpos x (le_of_lt hxpos))]
    exact hanti hε hxpos hx
  have hdensity :
      ContinuousOn
        (fun x : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρpos hρlt hκglob hcont hκzero
      hκbound hFzero hFrec hFpos hFbound
  have hsum (x : ℝ) (hx : 0 < x) :
      Summable (fun n : ℕ => F n x) :=
    renewal_density_series_summable_of_geometric_power_bound
      ρ x (le_of_lt hρpos) hρlt hx (fun n => F n x)
      (fun n => hFpos n x (le_of_lt hx))
      (fun n => hFbound n x hx)
  exact ⟨F, hFzero, hFrec, hdensity,
    causal_shifted_renewal_density_interval_integrable_at_zero
      F b hsum hInt⟩