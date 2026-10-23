-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_psi_volterra_denominator_of_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:21:44.235472+00:00
-- url     : https://prove2.me/submissions/c138a519-cd76-44fd-9705-e123deb07c7c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_esscher_shift_unit_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hroot : X.ψ φ = q)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂(X.ν.map (fun y : ℝ => -y))) < ⊤) :
    X.ψ (φ + θ) - q =
      θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)
        ∂(X.ν.map (fun y : ℝ => -y))) := by
  have hshift :=
    gaussian_laplaceExponent_esscher_shift_unit_atom
      X.c X.σ φ θ X.ν hφ hθ hlevy
  rw [← hroot]
  exact hshift
