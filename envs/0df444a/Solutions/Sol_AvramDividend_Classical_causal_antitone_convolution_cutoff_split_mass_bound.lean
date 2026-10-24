-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_convolution_cutoff_split_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:39:30.160059+00:00
-- url     : https://prove2.me/submissions/2795f736-11a3-49c4-9415-23085382bda9

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_convolution_split_integral_bound
import Theorems.Thm_AvramDividend_Classical_causal_antitone_reversed_kernel_cutoff_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_reversed_kernel_right_interval_mass_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A single cutoff kernel-mass bound controls both pieces of causal convolution. -/
theorem solution
    (κ F : ℝ → ℝ) (x u ρ P B : ℝ)
    (h0u : 0 ≤ u) (hux : u ≤ x) (hxu : 0 < x - u)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcutInt : IntervalIntegrable κ volume 0 (x - u))
    (hκcutMass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ)
    (hleftInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hFleft : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x, F s ≤ B)
    (hκright : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ P) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤
      (ρ / (x - u)) * P + B * ρ := by
  have hKleft : ∀ s ∈ Ioo (0 : ℝ) u,
      κ (x - s) ≤ ρ / (x - u) :=
    AvramDividend.Classical.causal_antitone_reversed_kernel_cutoff_mass_bound
      κ x u ρ hxu hanti hκcutInt hκcutMass
  have hMassRight :
      (∫ s in u..x, κ (x - s)) ≤ ρ := by
    rw [AvramDividend.Classical.causal_reversed_kernel_right_interval_mass_identity]
    exact hκcutMass
  exact AvramDividend.Classical.causal_convolution_split_integral_bound
    κ F x u (ρ / (x - u)) B P ρ
    h0u hux (div_nonneg hρ hxu.le) hB
    hleftInt hrightInt hFInt hκrightInt
    hKleft hFleft hFright hκright hFmass hMassRight
