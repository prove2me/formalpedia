-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:26:03.665144+00:00
-- url     : https://prove2.me/submissions/428f5fdf-83d0-4363-ae45-2684ed073a2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (theta delta : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    let Positive : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ R m i ω
        then Real.exp (theta*R m i ω) else 0
    let Square : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if delta ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0
    ∀ m ω, Signed m ω ≤ Positive m ω+(1/delta^2)*Square m ω := by
  classical
  intro Δ s R Signed Positive Square m ω
  let B : ℕ → Ω → Prop := fun i ω =>
    s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω
  have hFinite :=
    avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
      (Finset.range m) B (R m) theta delta hθ hδ ω
  have hSub (i : ℕ) :
      (if B i ω ∧ delta ≤ |R m i ω| then (R m i ω)^2 else 0) ≤
      (if s m i < ρ ω then
        (if delta ≤ |R m i ω| then (R m i ω)^2 else 0)
      else 0) := by
    by_cases hB : B i ω
    · have hs := hB.1
      simp [hB,hs]
    · by_cases hs : s m i < ρ ω
      · by_cases hLarge : delta ≤ |R m i ω|
        · simp [hB,hs,hLarge,sq_nonneg]
        · simp [hB,hs,hLarge]
      · simp [B,hB,hs]
  have hSum := Finset.sum_le_sum (s:=Finset.range m)
    (fun i hi => hSub i)
  have hc : 0 ≤ (1/delta^2) := by positivity
  have hMul := mul_le_mul_of_nonneg_left hSum hc
  dsimp only [Signed,Positive,Square,B] at *
  linarith [hFinite,hMul]
