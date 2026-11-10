-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:40:25.243616+00:00
-- url     : https://prove2.me/submissions/08881d64-e7fa-4f21-843b-eecb08efff69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        let z : ℕ → ℝ := fun i =>
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)
        let g : ℕ → ℝ := fun i =>
          X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
        (∀ i ∈ S, z i ∈ Set.Icc a b ∧
          z i + g i ∈ Set.Icc a b ∧
          z i ≠ z i + g i ∧
          dist (z i + g i) (z i) < δ) →
        |∑ i ∈ S,
          (w (z i + g i) -
            taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
              (z i) (z i + g i) -
            (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)| ≤
          ε * ∑ i ∈ S, (g i) ^ 2 := by
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω S s t
  let z : ℕ → ℝ := fun i =>
    Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)
  let g : ℕ → ℝ := fun i =>
    X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
  change
    (∀ i ∈ S, z i ∈ Set.Icc a b ∧
      z i + g i ∈ Set.Icc a b ∧
      z i ≠ z i + g i ∧
      dist (z i + g i) (z i) < δ) →
    |∑ i ∈ S,
      (w (z i + g i) -
        taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
          (z i) (z i + g i) -
        (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)| ≤
      ε * ∑ i ∈ S, (g i) ^ 2
  intro hcells
  have hterm (i : ℕ) (hi : i ∈ S) :
      |w (z i + g i) -
        taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
          (z i) (z i + g i) -
        (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2| ≤
        ε * (g i) ^ 2 := by
    obtain ⟨hz, hy, hne, hdist⟩ := hcells i hi
    have h := hTaylor ω (s i) (z i + g i) hz hy hne hdist
    have h' :
        |w (z i + g i) -
          taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
            (z i) (z i + g i) -
          (iteratedDeriv 2 w (z i) *
            ((z i + g i) - z i) ^ 2) / 2| ≤
          ε * ((z i + g i) - z i) ^ 2 := h
    have hsub : z i + g i - z i = g i := by ring
    simpa only [hsub] using h'
  calc
    |∑ i ∈ S,
      (w (z i + g i) -
        taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
          (z i) (z i + g i) -
        (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)| ≤
      ∑ i ∈ S, |w (z i + g i) -
        taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
          (z i) (z i + g i) -
        (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ε * (g i) ^ 2 :=
      Finset.sum_le_sum (by intro i hi; exact hterm i hi)
    _ = ε * ∑ i ∈ S, (g i) ^ 2 := by rw [Finset.mul_sum]
