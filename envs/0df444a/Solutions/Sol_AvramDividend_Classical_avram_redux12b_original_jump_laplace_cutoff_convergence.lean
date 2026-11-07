-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux12b_original_jump_laplace_cutoff_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:42:46.075825+00:00
-- url     : https://prove2.me/submissions/d9770024-3864-4fc5-82a7-1836d2280119

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux13_original_jump_cutoff_transform_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_redux13_source_levy_cutoff_exponent_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      Tendsto (fun k : ℕ =>
        (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P)) atTop (𝓝
        ((∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P))) ∧
      Tendsto (fun k : ℕ =>
        Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)))) atTop (𝓝
        (Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))))) := by
  intro n
  constructor
  · exact avram_redux13_original_jump_cutoff_transform_tendsto X hX hBV n
  · exact avram_redux13_source_levy_cutoff_exponent_tendsto X hX hBV n
