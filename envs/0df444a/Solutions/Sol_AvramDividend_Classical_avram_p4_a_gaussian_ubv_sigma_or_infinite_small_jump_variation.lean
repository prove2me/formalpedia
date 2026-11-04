-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_or_infinite_small_jump_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:45:13.27968+00:00
-- url     : https://prove2.me/submissions/bd41848e-c066-4cb2-b2bc-fc9f804a2639

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Lévy triplet's exhaustive UBV split. In the zero-Gaussian
branch the small negative jumps necessarily have infinite total variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    (0 < X.σ) ∨
      (X.σ = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) := by
  rcases lt_or_eq_of_le X.σ_nonneg with hσpos | hσzero
  · exact Or.inl hσpos
  · right
    have hz : X.σ = 0 := hσzero.symm
    refine ⟨hz, ?_⟩
    by_contra hnot
    have hfinite :
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
      lt_top_iff_ne_top.mpr hnot
    exact hBV ⟨hz, hfinite⟩
