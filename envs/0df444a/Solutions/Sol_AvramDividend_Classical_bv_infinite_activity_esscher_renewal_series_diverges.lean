-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_esscher_renewal_series_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:25:13.816348+00:00
-- url     : https://prove2.me/submissions/80e7ae32-68ae-42f9-8c53-153b7abd1bce

import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The geometric renewal series dominates its diverging positive kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      Integrable κ volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  obtain ⟨κ, ρ, _, hρpos, hρone, hcont, hanti, hκzero, hκnonneg,
    hκL1, hmass, hκdiv⟩ :=
    bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
      X hX hbv q hq φ hφ hroot hInfinite
  have hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t := by
    intro t _
    exact hκnonneg t
  obtain ⟨hκglobal, F, hFzero, hFsucc, hFL1, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package κ ρ
      hρpos hρone hcont hanti hκzero hκpos hκL1 hmass
  have hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x) := by
    intro x hx
    apply renewal_density_series_summable_of_geometric_power_bound
      ρ x (le_of_lt hρpos) hρone hx (fun n : ℕ => F n x)
    · intro n
      exact hFpos n x (le_of_lt hx)
    · intro n
      exact hFbound n x hx
  have hseries :
      Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    apply esscher_positive_renewal_tsum_tendsto_top
      κ (fun x n => F n x) hκdiv hsum
    · intro x _
      simpa only [hFzero]
    · intro x hx n
      exact hFpos n x (le_of_lt hx)
  exact ⟨κ, ρ, F, hρpos, hρone, hcont, hanti, hκzero,
    hκnonneg, hκglobal, hmass, hFzero, hFsucc, hFL1,
    hFpos, hFbound, hseries⟩
