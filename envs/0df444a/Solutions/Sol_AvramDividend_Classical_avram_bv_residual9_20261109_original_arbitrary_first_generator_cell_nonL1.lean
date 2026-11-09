-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_20261109_original_arbitrary_first_generator_cell_nonL1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:08:33.695715+00:00
-- url     : https://prove2.me/submissions/9ff70541-2f9b-4e32-ba6a-3a11686b2050

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ¬ Integrable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
      (∑ i ∈ Finset.range (0 + 1),
        if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u 0 i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u 0 (i + 1) : ℝ) - (u 0 i : ℝ))
        else 0)) P := by
  intro hI
  have hzero : u 0 0 = 0 := (hgrid 0).1
  have hone : (u 0 1 : ℝ) = T / 2 := by
    have hh := (hgrid 0).2
    norm_num at hh
    linarith
  have hcell := avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
    X q T x hT w C D hruin hpositive hcap hmeas hnonint
  apply hcell
  simpa [Finset.sum_range_one, hzero, hone] using hI.hasFiniteIntegral
