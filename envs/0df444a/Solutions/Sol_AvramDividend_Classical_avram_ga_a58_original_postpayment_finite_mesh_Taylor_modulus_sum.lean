-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:04:34.817675+00:00
-- url     : https://prove2.me/submissions/53dd9ec5-9f56-480b-8896-e008b65113b5

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s : ℕ → ℝ≥0) (y : ℕ → ℝ),
        let z : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        (∀ i ∈ S, z i ∈ Icc a b ∧ y i ∈ Icc a b ∧
          z i ≠ y i ∧ dist (y i) (z i) < δ) →
        |∑ i ∈ S, (w (y i) -
          taylorWithinEval w 1 (uIcc (z i) (y i)) (z i) (y i) -
          (iteratedDeriv 2 w (z i) * (y i - z i) ^ 2) / 2)| ≤
        ε * ∑ i ∈ S, (y i - z i) ^ 2 := by
  intro ε hε
  obtain ⟨ δ, hδ, hpoint ⟩ :=
    avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨ δ, hδ, ?_ ⟩
  intro ω S s y z hcell
  have hOne (i : ℕ) (hi : i ∈ S) :
      |w (y i) - taylorWithinEval w 1 (uIcc (z i) (y i))
        (z i) (y i) -
        (iteratedDeriv 2 w (z i) * (y i - z i) ^ 2) / 2| ≤
      ε * (y i - z i) ^ 2 := by
    obtain ⟨ hzi, hyi, hne, hdist ⟩ := hcell i hi
    simpa only [z] using
      (hpoint ω (s i) (y i) hzi hyi hne hdist)
  calc
    |∑ i ∈ S, (w (y i) -
      taylorWithinEval w 1 (uIcc (z i) (y i)) (z i) (y i) -
      (iteratedDeriv 2 w (z i) * (y i - z i) ^ 2) / 2)| ≤
        ∑ i ∈ S, |w (y i) -
          taylorWithinEval w 1 (uIcc (z i) (y i)) (z i) (y i) -
          (iteratedDeriv 2 w (z i) * (y i - z i) ^ 2) / 2| :=
      Finset.abs_sum_le_sum_abs _ S
    _ ≤ ∑ i ∈ S, ε * (y i - z i) ^ 2 := by
      exact Finset.sum_le_sum (fun i hi => hOne i hi)
    _ = ε * ∑ i ∈ S, (y i - z i) ^ 2 := by
      rw [Finset.mul_sum]
