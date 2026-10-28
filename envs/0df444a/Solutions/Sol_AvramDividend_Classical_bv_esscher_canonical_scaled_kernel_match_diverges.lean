-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_canonical_scaled_kernel_match_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:46:44.344917+00:00
-- url     : https://prove2.me/submissions/e2ecdd19-9ffc-41a4-a3f4-aaeb89882703

import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The exact BV Esscher kernel matching the scaled jump-tail measure diverges at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (ENNReal.ofReal X.drift)⁻¹ •
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) =
        (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (κ t)) ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  obtain ⟨κ, ρ, hκdef, hρpos, hρlt, hcont, hanti, hzero,
      hκpos, hκint, hmass, hmeasure⟩ :=
    bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
      X hX hbv q hq φ hφ hroot
  obtain ⟨κ', ρ', hκ'def, _, _, _, _, _, _, _, _, htop⟩ :=
    bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
      X hX hbv q hq φ hφ hroot hInfinite
  have heq : κ = κ' := by
    funext t
    exact (hκdef t).trans (hκ'def t).symm
  have hκtop : Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    rw [heq]
    exact htop
  exact ⟨κ, ρ, hρpos, hρlt, hcont, hanti, hzero, hκpos,
    hκint, hmass, hmeasure, hκtop⟩