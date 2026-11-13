-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a59_original_pathwise_uniform_C2_mesh_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:26:53.826995+00:00
-- url     : https://prove2.me/submissions/55100db2-e8e6-46a7-bc10-2fc3090151d7

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The uniform C2 Taylor modulus and bounded squared increments imply vanishing mesh error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ω : Ω) (S : ℕ → Finset ℕ)
    (s : ℕ → ℕ → ℝ≥0) (y : ℕ → ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) :
    let z : ℕ → ℕ → ℝ := fun m i =>
      x + X.X (s m i) ω - rightLimit D (s m i) ω
    (∀ m i, i ∈ S m → z m i ∈ Icc a b ∧
      y m i ∈ Icc a b ∧ z m i ≠ y m i) →
    (∀ δ : ℝ, 0 < δ → ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m → ∀ i ∈ S m,
        dist (y m i) (z m i) < δ) →
    (∀ m : ℕ, (∑ i ∈ S m, (y m i - z m i) ^ 2) ≤ K) →
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
      |∑ i ∈ S m, (w (y m i) -
        taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
        (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤ ε := by
  intro z hcell hsmall henergy ε hε
  have hK1 : 0 < K + 1 := by linarith
  have hε0 : 0 < ε / (K + 1) := div_pos hε hK1
  obtain ⟨δ, hδ, hmod⟩ :=
    avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
      X x D hD C w hw a b ha hab hbcap (ε / (K + 1)) hε0
  obtain ⟨k, hk⟩ := hsmall δ hδ
  have hscale : (ε / (K + 1)) * K ≤ ε := by
    calc
      (ε / (K + 1)) * K = (ε * K) / (K + 1) := by ring
      _ ≤ ε := (div_le_iff₀ hK1).2 (by nlinarith)
  refine ⟨k, ?_⟩
  intro m hm
  have hmodm :
      |∑ i ∈ S m, (w (y m i) -
        taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
        (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤
      (ε / (K + 1)) * ∑ i ∈ S m, (y m i - z m i) ^ 2 := by
    simpa only [z] using
      (hmod ω (S m) (s m) (y m) (by
        intro i hi
        obtain ⟨hzi, hyi, hne⟩ := hcell m i hi
        exact ⟨hzi, hyi, hne, hk m hm i hi⟩))
  calc
    |∑ i ∈ S m, (w (y m i) -
      taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
      (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤
        (ε / (K + 1)) * ∑ i ∈ S m, (y m i - z m i) ^ 2 := hmodm
    _ ≤ (ε / (K + 1)) * K :=
      mul_le_mul_of_nonneg_left (henergy m) (le_of_lt hε0)
    _ ≤ ε := hscale
