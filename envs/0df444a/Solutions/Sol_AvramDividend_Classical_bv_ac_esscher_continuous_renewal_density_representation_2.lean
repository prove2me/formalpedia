-- Prove2me | solution 2 for AvramDividend.Classical.bv_ac_esscher_continuous_renewal_density_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:49:42.726044+00:00
-- url     : https://prove2.me/submissions/cae3a70e-cffc-4089-bec5-57eac66f0193

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_renewal_kernel_series_data
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Extract the positive-time continuous density using the correctly scaled
Esscher renewal series. -/
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
  rcases bv_ac_esscher_scaled_renewal_kernel_series_data
    X hX q hq W hW hbv hac with
    ⟨φ, c, ρ, b, κ, F, hφ, hroot, hρ0, hρ1,
     hκint, hκcont, hκzero, hκbound,
     hF0, hFsucc, hFnonneg, hFpoint, hFint, hFeq⟩
  have hG : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint
  have hb : ContinuousOn (fun _ : ℝ => b) (Ioi (0 : ℝ)) :=
    continuousOn_const
  refine ⟨φ, c, (fun x : ℝ => b * ∑' n : ℕ,
    if n = 0 then (0 : ℝ) else F (n - 1) x),
    hφ, hroot, ?_, hFint, hFeq⟩
  exact hb.mul hG
