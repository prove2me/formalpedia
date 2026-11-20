-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:40.6384+00:00
-- url     : https://prove2.me/submissions/42a935d0-e3c2-40d6-bccb-ba403f84ab56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (j : ℕ) (ω : Ω) :
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range (m j),
      E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
        (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
          X.generator w (Y (v i)) - q * w (Y (v i))
         else 0)) ≤ 0 := by
  dsimp only
  refine Finset.sum_nonpos ?_
  intro i hi
  have he : 0 ≤ Real.exp (-(q * ((min (u j (i + 1)) (σ ω) : ℝ≥0) : ℝ))) :=
    (Real.exp_pos _).le
  have hd : 0 ≤
      (((min (u j (i + 1)) (σ ω) -
        min (u j i) (σ ω) : ℝ≥0) : ℝ)) :=
    NNReal.coe_nonneg _
  have hg :
      (if 0 < x + X.X (min (u j i) (σ ω)) ω -
                rightLimit D (min (u j i) (σ ω)) ω ∧
          ENNReal.ofReal (x + X.X (min (u j i) (σ ω)) ω -
            rightLimit D (min (u j i) (σ ω)) ω) < C then
        X.generator w (x + X.X (min (u j i) (σ ω)) ω -
          rightLimit D (min (u j i) (σ ω)) ω) -
          q * w (x + X.X (min (u j i) (σ ω)) ω -
            rightLimit D (min (u j i) (σ ω)) ω)
       else 0) ≤ 0 := by
    split_ifs with h
    · exact (hw_gen _ h.1 h.2).2
    · exact le_refl 0
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg he hd) hg
