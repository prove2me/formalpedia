-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:37:41.061195+00:00
-- url     : https://prove2.me/submissions/0b02e0d4-9baa-4db4-a105-7cbaf011727d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
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
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (theta delta : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    (∀ m, Integrable (Signed m) P) →
      Tendsto (fun m => ∫ ω, Signed m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  intro Δ s R Signed hSI
  let Positive : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ R m i ω
      then Real.exp (theta*R m i ω) else 0
  let Square : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then
        (if delta ≤ |R m i ω| then (R m i ω)^2 else 0)
      else 0
  have hP := avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
    X hν hσ n hn ρ hρstop theta delta hθ hδ
  have hPI : ∀ m, Integrable (Positive m) P := by
    simpa only [Positive,R,s,Δ,← ite_and] using hP.1
  have hPLim : Tendsto
      (fun m => ∫ ω, Positive m ω ∂P) atTop (𝓝 (0:ℝ)) := by
    simpa only [Positive,R,s,Δ,← ite_and] using hP.2
  have hQI : ∀ m, Integrable (Square m) P := by
    simpa only [Square,R,s,Δ] using
      (avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
        X hν n ρ hρstop delta)
  have hQLim : Tendsto
      (fun m => ∫ ω, Square m ω ∂P) atTop (𝓝 (0:ℝ)) := by
    simpa only [Square,R,s,Δ] using
      (avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
        X hν hσ n ρ hρstop delta hδ)
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ Signed m ω := by
    dsimp [Signed]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hBound (m : ℕ) (ω : Ω) :
      Signed m ω ≤ Positive m ω+(1/delta^2)*Square m ω := by
    simpa only [Signed,Positive,Square,R,s,Δ] using
      (avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
        X n ρ theta delta hθ hδ m ω)
  exact avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
    P Signed Positive Square (1/delta^2) (by positivity)
    hSI hPI hQI hPos hBound hPLim hQLim
