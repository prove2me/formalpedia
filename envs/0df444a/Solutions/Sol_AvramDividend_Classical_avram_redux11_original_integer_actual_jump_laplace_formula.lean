-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux11_original_integer_actual_jump_laplace_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:42:14.677905+00:00
-- url     : https://prove2.me/submissions/7860ee53-088a-4e8c-8351-36adff778c67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux12b_original_jump_laplace_finite_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_redux12b_original_jump_laplace_cutoff_convergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))) := by
  intro n
  have hcut :=
    avram_redux12b_original_jump_laplace_finite_cutoff X hX hBV n
  obtain ⟨hL, hR⟩ :=
    avram_redux12b_original_jump_laplace_cutoff_convergence X hX hBV n
  have hfun :
      (fun k : ℕ => (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P)) =
      (fun k : ℕ => Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)))) := by
    funext k
    exact hcut k
  rw [hfun] at hL
  exact tendsto_nhds_unique hL hR
