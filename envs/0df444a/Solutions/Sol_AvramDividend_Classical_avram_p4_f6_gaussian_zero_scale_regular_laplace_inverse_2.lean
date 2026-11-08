-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:33:04.302841+00:00
-- url     : https://prove2.me/submissions/219c7466-c802-4e45-a52b-5682e7cdcfbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_ladder_renewal_cdf_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ W₀ : ℝ → ℝ,
      (∀ y < 0, W₀ y = 0) ∧
      (∀ y, 0 ≤ y → 0 ≤ W₀ y) ∧
      ContinuousOn W₀ (Ici 0) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
        IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
        ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y =
          (X.ψ θ)⁻¹) := by
  obtain ⟨ν, hSupp, hAtom, hFin, hLap⟩ :=
    avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists X hX hσ
  exact avram_p4_f6_gaussian_ladder_renewal_cdf_laplace
    X hX hσ ν hSupp hAtom hFin hLap
