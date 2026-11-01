-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:51:03.605718+00:00
-- url     : https://prove2.me/submissions/aac03493-8fe9-4dec-bcf3-8c5c99d3a8c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- On each actual original Lévy sample, the full Stieltjes integral of
right-cell source-exponential step weights is exactly its finite-grid sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ) (u : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) (hD : IsDividendStrategy 𝓕 D) :
    (∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal *
      (θ * Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) := by
  classical
  let μ : Measure ℝ := dividendMeasure D ω
  let E : ℕ → Set ℝ := fun i => Ioc (u i : ℝ) (u (i + 1) : ℝ)
  let a : ℕ → ℝ := fun i => θ *
    Real.exp (θ * X.X (u (i + 1)) ω - (u (i + 1) : ℝ) * X.ψ θ) *
    Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
  have hfinite (i : ℕ) : μ (E i) ≠ ⊤ := by
    change dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ)) ≠ ⊤
    rw [dividendMeasure_Ioc_rightLimit D hD ω (u i) (u (i + 1))]
    exact ENNReal.ofReal_ne_top
  have hInt (i : ℕ) :
      Integrable (fun s : ℝ => if s ∈ E i then a i else 0) μ := by
    have hc : IntegrableOn (fun _ : ℝ => a i) (E i) μ := by
      apply integrableOn_const
      exact hfinite i
      · exact enorm_ne_top
    have hi := hc.integrable_indicator measurableSet_Ioc
    have heq : (fun s : ℝ => if s ∈ E i then a i else 0) =
        (E i).indicator (fun _ => a i) := by
      funext s
      by_cases hs : s ∈ E i <;> simp [Set.indicator, hs]
    rw [heq]
    exact hi
  change (∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ E i then a i else 0 ∂μ) =
      ∑ i ∈ Finset.range n, (μ (E i)).toReal * a i
  rw [integral_finset_sum (Finset.range n) (fun i hi => hInt i)]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (fun s : ℝ => if s ∈ E i then a i else 0) =
      (E i).indicator (fun _ => a i) := by
    funext s
    by_cases hs : s ∈ E i <;> simp [Set.indicator, hs]
  rw [heq]
  simpa only [Measure.real, smul_eq_mul] using
    (integral_indicator_const (a i) (s := E i) measurableSet_Ioc)