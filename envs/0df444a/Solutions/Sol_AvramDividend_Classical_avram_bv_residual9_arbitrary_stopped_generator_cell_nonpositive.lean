-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_arbitrary_stopped_generator_cell_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:52:26.092516+00:00
-- url     : https://prove2.me/submissions/0e4a988d-0bfa-4151-8e02-bb76fe5103d0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original HJB generator cells are pathwise nonpositive on any monotone
    physical grid; no mesh-refinement or stochastic L1 claim is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ n i, i < n + 1 → ∀ ω,
      (let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
       if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z i ∧ ENNReal.ofReal (Z i) < C then
         Real.exp (-(q * (u n i : ℝ))) *
           (X.generator w (Z i) - q * w (Z i)) *
           ((u n (i + 1) : ℝ) - (u n i : ℝ))
       else 0) ≤ 0 := by
  intro n i hi ω
  dsimp
  let Z : ℕ → ℝ := fun j => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
  split_ifs with hmask
  ·
    have hgap : X.generator w (Z i) - q * w (Z i) ≤ 0 :=
      (hw_gen (Z i) hmask.2.1 hmask.2.2).2
    have hstep : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
      exact_mod_cast hmono n i hi
    have hwidth :
        0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) :=
      sub_nonneg.mpr hstep
    have hweight : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
      (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hweight hgap) hwidth
  · exact le_refl _
