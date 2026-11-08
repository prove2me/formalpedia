-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_uniform_first_generator_cell_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:29:55.92408+00:00
-- url     : https://prove2.me/submissions/5cc35ab9-0d40-4a17-a660-8b70cf68db8e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_origin_postright_surplus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The zeroth stopped generator cell samples the exact post-dividend reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    (let Z : ℕ → ℝ := fun j => Function.leftLim
       (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
     if (u n 0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z 0 ∧ ENNReal.ofReal (Z 0) < C then
       Real.exp (-(q * (u n 0 : ℝ))) *
         (X.generator w (Z 0) - q * w (Z 0)) *
         ((u n 1 : ℝ) - (u n 0 : ℝ))
     else 0) =
    (if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
         0 < x - rightLimit D 0 ω ∧
         ENNReal.ofReal (x - rightLimit D 0 ω) < C then
       (X.generator w (x - rightLimit D 0 ω) -
           q * w (x - rightLimit D 0 ω)) *
         (T / ((n : ℝ) + 2))
     else 0) := by
  have hwidth : (u n 1 : ℝ) - (u n 0 : ℝ) = T / ((n : ℝ) + 2) := by
    rw [huniform n 1, huniform n 0]
    simp
  have hreserve := avram_a19_origin_postright_surplus X x D u hgrid0 n ω
  dsimp only
  simp only [hreserve, hwidth]
  simp [hgrid0 n]
