-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:20.844068+00:00
-- url     : https://prove2.me/submissions/1da0ab9b-8bd5-4ae7-ab17-11a88b468365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The explicit source-faithful inverse-grid estimate implies the finite-cap localization estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M : ℕ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ m : ℕ,
        (P.prod volume)
          {z : Ω × ℝ |
            0 < z.2 ∧ z.2 < (n : ℝ) ∧
            x + X.X (Real.toNNReal z.2) z.1 -
              rightLimit D (Real.toNNReal z.2) z.1 = b ∧
            D n z.1 - D 0 z.1 ≤ (M : ℝ)} ≤
          (C : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
      X hBV hν
  let C : NNReal := Real.toNNReal
    (1 + (M : ℝ) + 2 * (n : ℝ) / (X.σ * Real.sqrt (2 * Real.pi)))
  have hden : 0 < X.σ * Real.sqrt (2 * Real.pi) := by positivity
  have hp : 0 < 1 + (M : ℝ) +
      2 * (n : ℝ) / (X.σ * Real.sqrt (2 * Real.pi)) := by positivity
  have hC : 0 < C := Real.toNNReal_pos.mpr hp
  refine ⟨C, hC, ?_⟩
  intro m
  by_cases hm : m = 0
  · subst m
    have hnz : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
    simpa [ENNReal.inv_zero, ENNReal.mul_top, hnz] using
      (show (P.prod volume)
          {z : Ω × ℝ |
            0 < z.2 ∧ z.2 < (n : ℝ) ∧
            x + X.X (Real.toNNReal z.2) z.1 -
              rightLimit D (Real.toNNReal z.2) z.1 = b ∧
            D n z.1 - D 0 z.1 ≤ (M : ℝ)} ≤ ⊤ from le_top)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    simpa only [C] using
      (avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
        X hBV hν x b D hD n M m hmpos)
