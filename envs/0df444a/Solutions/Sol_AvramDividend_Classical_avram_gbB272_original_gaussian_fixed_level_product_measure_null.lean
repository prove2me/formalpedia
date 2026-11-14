-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB272_original_gaussian_fixed_level_product_measure_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:42.488896+00:00
-- url     : https://prove2.me/submissions/53870a9c-0df8-4bf0-8c3c-221e1468a2a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB273_ennreal_mass_zero_of_finite_inverse_nat_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open Filter
open scoped NNReal ENNReal
noncomputable section

/-- The finite-grid localized mass bounds imply null original product occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} = 0 := by
  have hGrid := avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound X hBV hν x b D hD n
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b}
  let T : ℕ → Set (Ω × ℝ) := fun M => {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  have hNull : ∀ M : ℕ, (P.prod volume) (T M) = 0 := by
    intro M
    obtain ⟨C, hCpos, hBounds⟩ := hGrid M
    exact avram_gbB273_ennreal_mass_zero_of_finite_inverse_nat_bounds ((P.prod volume) (T M)) C hBounds
  have hCover : S ⊆ ⋃ M : ℕ, T M := by
    rintro z ⟨h0, hn, hEq⟩
    obtain ⟨M, hM⟩ := exists_nat_ge (D n z.1 - D 0 z.1)
    exact Set.mem_iUnion.mpr ⟨M, ⟨h0, hn, hEq, hM⟩⟩
  have hUnion : (P.prod volume) (⋃ M : ℕ, T M) = 0 := by
    exact measure_iUnion_null hNull
  exact le_antisymm ((measure_mono hCover).trans_eq hUnion) bot_le
