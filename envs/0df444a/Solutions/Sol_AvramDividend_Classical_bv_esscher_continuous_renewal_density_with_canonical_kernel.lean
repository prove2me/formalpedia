-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_continuous_renewal_density_with_canonical_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:01:17.057579+00:00
-- url     : https://prove2.me/submissions/b872104e-5918-4db3-867a-adc56653d9fb

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < φ ∧ X.ψ φ = q ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      f = (fun y : ℝ =>
        b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y) ∧
      ContinuousOn f (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x, f y) := by
  obtain ⟨φ, c, ρ, b, κ, F, hκdef, hφ, hroot, hρ0, hρ1, hκint,
    hκcont, hκzero, hκbound, hF0, hFsucc, hFnonneg, hFpoint,
    hFint, hrepr⟩ :=
    bv_esscher_scaled_renewal_kernel_series_data_with_pointwise X hX q hq W hW hbv
  have hc : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint
  exact ⟨φ, c, ρ, b, κ, F, (fun y : ℝ =>
    b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y),
    hκdef, hφ, hroot, hF0, hFsucc, hFnonneg, rfl,
    continuousOn_const.mul hc, hFint, hrepr⟩
