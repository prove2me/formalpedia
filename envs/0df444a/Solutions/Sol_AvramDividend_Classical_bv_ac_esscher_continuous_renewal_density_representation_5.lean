-- Prove2me | solution 5 for AvramDividend.Classical.bv_ac_esscher_continuous_renewal_density_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:59:24.991453+00:00
-- url     : https://prove2.me/submissions/4a8b667f-5f1a-4431-9cfd-b47fea0ee3eb

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_renewal_kernel_series_data
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A constant multiple of the continuous renewal density gives the BV Esscher scale representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c : ℝ) (f : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      ContinuousOn f (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x, f y) := by
  obtain ⟨φ, c, ρ, b, κ, F, hφ, hroot, hρ0, hρ1, hκint,
    hκcont, hκzero, hκbound, hF0, hFsucc, hFnonneg, hFpoint,
    hFint, hrepr⟩ :=
    bv_ac_esscher_scaled_renewal_kernel_series_data X hX q hq W hW hbv hac
  have hc : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint
  exact ⟨φ, c, (fun y : ℝ =>
    b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y),
    hφ, hroot, continuousOn_const.mul hc, hFint, hrepr⟩
