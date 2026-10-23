-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_psi_strictly_above_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:45:19.882984+00:00
-- url     : https://prove2.me/submissions/962d803e-7ef7-4dcd-a920-e0fbecb2a4df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_inclusive_drift_adjusted
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_resolvent_denominator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hθ : 0 < θ) (hσ : 0 < X.σ) (hroot : X.ψ φ = q)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(X.ν.map (fun y : ℝ => -y))) < ⊤) :
    q < X.ψ (φ + θ) := by
  let μ : Measure ℝ := X.ν.map (fun y : ℝ => -y)
  let b : ℝ := X.c - μ.real ({1} : Set ℝ)
  let a : ℝ := X.σ ^ 2 / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hψ (r : ℝ) (hr : 0 ≤ r) :
      X.ψ r =
        b * r + a * r ^ 2 +
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-r * z) - 1 +
              r * (if z ≤ 1 then z else 0) ∂μ) := by
    simp only [SpectrallyNegativeLevy.ψ, μ, b, a]
    convert gaussian_laplaceExponent_inclusive_drift_adjusted
      X.c X.σ r X.ν hr hlevy using 1 <;> ring
  have hroot' :
      b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ) = q :=
    (hψ φ hφ.le).symm.trans hroot
  have hpos :
      0 < (b * (φ + θ) + a * (φ + θ) ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-(φ + θ) * z) - 1 +
            (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q :=
    gaussian_positive_root_resolvent_denominator
      μ b a q φ θ ha hq hφ hθ hlevy hroot'
  rw [hψ (φ + θ) (add_nonneg hφ.le hθ.le)]
  exact sub_pos.mp hpos
