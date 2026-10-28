-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_antitone_subunit_convolution_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:22:59.490883+00:00
-- url     : https://prove2.me/submissions/8cda0396-b0cb-4ee9-a048-4cbc3b2aac92

import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_antitone_Ioc_powers_quadratic
import Theorems.Thm_AvramDividend_Classical_positive_nonnegative_interval_integral_le_global
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Package geometric quadratic pointwise bounds for convolution powers of
a positive-time continuous antitone kernel of subunit integral mass. -/
theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by
  obtain ⟨F, hF0, hFsucc, hFL1, hFpos, hFmass⟩ :=
    causal_positive_convolution_powers_geometric_truncated_mass
      κ hκL1 hκpos
  have hKmass : ∀ y : ℝ, 0 ≤ y →
      (∫ t in Ioc (0 : ℝ) y, κ t ∂volume) ≤ ρ := by
    intro y hy
    calc
      (∫ t in Ioc (0 : ℝ) y, κ t ∂volume) ≤
          (∫ t in Ioi (0 : ℝ), κ t ∂volume) :=
        positive_nonnegative_interval_integral_le_global
          κ hκL1 (fun t ht => hκpos t (le_of_lt ht)) y hy
      _ = ρ := hmass
  have hFmass' : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in Ioc (0 : ℝ) u, F n s ∂volume) ≤
        ρ ^ (n + 1) := by
    intro n u hu
    simpa only [hmass] using hFmass n u hu
  have hpoint := causal_antitone_Ioc_powers_quadratic
    κ F ρ hρpos.le hanti hcont hκpos hκL1 hKmass
    hF0 hFsucc hFpos hFL1 hFmass'
  exact ⟨F, hF0, hFsucc, hFL1, hFpos, hpoint⟩
