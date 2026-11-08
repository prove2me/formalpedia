-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_uniform_zero_row_B_nonintegrable_of_source_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:56:36.349499+00:00
-- url     : https://prove2.me/submissions/b780e0a3-6a0f-4a60-a1b8-e8de46cfa320

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (B : ℕ → Ω → ℝ) (K : Ω → ℝ)
    (hB0 : ∀ ω, B 0 ω =
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω)
    (hK : Integrable K P) : ¬ Integrable (B 0) P := by
  have hcell : ¬ HasFiniteIntegral (fun ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
      if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (0 : ℝ))) *
          (X.generator w Z - q * w Z) * (T / 2)
      else 0) P :=
    avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
      X q T x hT w C D hruin hpositive hcap hmeas hnonint
  intro hB
  have hdiff : Integrable (fun ω => B 0 ω - K ω) P := hB.sub hK
  have heq : (fun ω => B 0 ω - K ω) = (fun ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
      if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (0 : ℝ))) *
          (X.generator w Z - q * w Z) * (T / 2)
      else 0) := by
    funext ω
    rw [hB0 ω]
    ring
  rw [heq] at hdiff
  exact hcell hdiff.2
