-- Prove2me | solution 3 for AvramDividend.Classical.bv_ac_esscher_continuous_renewal_density_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:28:54.59691+00:00
-- url     : https://prove2.me/submissions/6eaec13a-a84f-4fad-985f-73f2ff424847
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_renewal_kernel_series_data
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  obtain ⟨φ, c, ρ, κ, F, hφ, hroot, hρ0, hρ1,
      hκint, hκcont, hκzero, hκbound, hF0, hFsucc,
      hFnonneg, hFpoint, hInterval, hRepresentation⟩ :=
    bv_ac_esscher_renewal_kernel_series_data X hX q hq W hW hbv hac
  refine ⟨φ, c,
    (fun x : ℝ => ∑' n : ℕ,
      if n = 0 then (0 : ℝ) else F (n - 1) x),
    hφ, hroot, ?_, hInterval, hRepresentation⟩
  exact causal_renewal_density_continuous_of_convolution_bounds
    κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
    hF0 hFsucc hFnonneg hFpoint
