-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:36:31.364853+00:00
-- url     : https://prove2.me/submissions/f1ce2775-cbaa-4ae9-8425-38019ed5c137

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact source-dependent Stieltjes integration of finite right-cell weights;
each cell includes all diffuse and right-atomic dividendMeasure mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ) (u : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      ENNReal.ofReal (θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) *
      dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ)) := by
  classical
  let μ : Measure ℝ := dividendMeasure D ω
  let E : ℕ → Set ℝ := fun i => Ioc (u i : ℝ) (u (i + 1) : ℝ)
  let a : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (θ *
    Real.exp (θ * X.X (u (i + 1)) ω - (u (i + 1) : ℝ) * X.ψ θ) *
    Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
  have hmeas (i : ℕ) :
      Measurable (fun s : ℝ => if s ∈ E i then a i else 0) :=
    Measurable.ite measurableSet_Ioc measurable_const measurable_const
  change (∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
    if s ∈ E i then a i else 0 ∂μ) =
      ∑ i ∈ Finset.range n, a i * μ (E i)
  rw [lintegral_finset_sum (Finset.range n) (fun i hi => hmeas i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hif : (fun s : ℝ => if s ∈ E i then a i else 0) =
      (E i).indicator (fun _ => a i) := by
    funext s
    by_cases hs : s ∈ E i <;> simp [Set.indicator, hs]
  rw [hif]
  exact lintegral_indicator_const measurableSet_Ioc (a i)