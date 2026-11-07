-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux13_original_jump_cutoff_transform_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:16:39.547534+00:00
-- url     : https://prove2.me/submissions/9940d27a-b493-4714-96b4-b23f6fea745d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux15_original_jump_cutoff_exponential_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_redux15_original_jump_cutoff_exp_ae_measurable
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
        else 0).toReal)) ∂P))) := by
  intro n
  letI : IsProbabilityMeasure P := X.isProbability
  let J : ℕ → Ω → ℝ≥0∞ := fun k ω => (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0)
  let K : Ω → ℝ≥0∞ := fun ω => (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0)
  let F : ℕ → Ω → ℝ := fun k ω => Real.exp (-(J k ω).toReal)
  let f : Ω → ℝ := fun ω => Real.exp (-(K ω).toReal)
  have hM : ∀ k, AEStronglyMeasurable (F k) P := by
    intro k
    simpa only [F, J] using
      avram_redux15_original_jump_cutoff_exp_ae_measurable X n k
  have hL : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (f ω)) := by
    simpa only [F, J, f, K] using
      avram_redux15_original_jump_cutoff_exponential_ae_tendsto X hBV n
  have hB : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ (1 : ℝ) := by
    intro k
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hJ : 0 ≤ (J k ω).toReal := ENNReal.toReal_nonneg
    have hExp : Real.exp (-(J k ω).toReal) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (neg_nonpos.mpr hJ)
      simpa using h
    simpa only [F, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)] using hExp
  have hI : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hD := tendsto_integral_of_dominated_convergence
    (bound := fun _ : Ω => (1 : ℝ)) hM hI hB hL
  simpa only [F, J, f, K] using hD
