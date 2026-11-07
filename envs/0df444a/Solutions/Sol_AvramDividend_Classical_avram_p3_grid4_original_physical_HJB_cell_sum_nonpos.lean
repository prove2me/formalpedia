-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:28:15.193688+00:00
-- url     : https://prove2.me/submissions/f8eb8ddb-5bfd-4a4f-9d43-849dc9387c97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The genuine generator component is nonpositive on each active physical cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
    (∑ i ∈ Finset.range (n + 1),
      if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u (i + 1) : ℝ) - (u i : ℝ))
      else 0) ≤ 0 := by
  dsimp
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with h
  · have hgen := (hw_gen _ h.2.1 h.2.2).2
    have hexp : 0 ≤ Real.exp (-(q * (u i : ℝ))) := (Real.exp_pos _).le
    have htime : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hmono i (Finset.mem_range.mp hi))
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hexp hgen) htime
  · simp
