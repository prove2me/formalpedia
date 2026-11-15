-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_compact_preleft_C2_physical_mesh_expected_L1_remainder_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:15:37.292209+00:00
-- url     : https://prove2.me/submissions/b3466260-8d9f-4991-a60c-0a51cdd09b04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
import Theorems.Thm_AvramDividend_Classical_avram_b24_uniform_quadratic_energy_absorption_L1_error_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (M : ℝ) :
    let z : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s k i)
    let g : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      X.X (t k i) ω - X.X (s k i) ω -
        ((t k i - s k i : ℝ≥0) : ℝ) * X.c
    let R : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ S k,
      (w (z k ω i + g k ω i) -
        taylorWithinEval w 1
          (Set.uIcc (z k ω i) (z k ω i + g k ω i))
          (z k ω i) (z k ω i + g k ω i) -
        (iteratedDeriv 2 w (z k ω i) * (g k ω i)^2) / 2)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ S k, (g k ω i)^2
    (∀ k, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
      z k ω i ∈ Icc a b ∧ z k ω i + g k ω i ∈ Icc a b ∧
        z k ω i ≠ z k ω i + g k ω i) →
    (∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
        dist (z k ω i + g k ω i) (z k ω i) < δ) →
    (∀ k, AEStronglyMeasurable (Q k) (P.restrict A)) →
    (∀ k, AEStronglyMeasurable (fun ω => |R k ω|) (P.restrict A)) →
    (0 ≤ M) →
    (∀ k, (∫ ω in A, Q k ω ∂P) ≤ M) →
    Tendsto (fun k => ∫ ω in A, |R k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro z g R Q hBand hSmall hQM hRM hM hEnergy
  have hQnonneg (k : ℕ) (ω : Ω) : 0 ≤ Q k ω := by
    dsimp [Q]
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  have hQabs (k : ℕ) : (fun ω => |Q k ω|) = Q k := by
    funext ω
    exact abs_of_nonneg (hQnonneg k ω)
  have hQB (k : ℕ) : (∫ ω in A, |Q k ω| ∂P) ≤ M := by
    simpa only [hQabs k] using hEnergy k
  have hAbsorb (ε : ℝ) (hε : 0 < ε) :
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        (∫ ω in A, |R k ω| ∂P) ≤
          ε * (∫ ω in A, |Q k ω| ∂P) := by
    obtain ⟨K, hK⟩ :=
      avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
        X x D hD C w hw a b ha hab hbcap A S s t
        hBand hSmall hQM hRM ε hε
    refine ⟨K, ?_⟩
    intro k hk
    simpa only [hQabs k] using hK k hk
  exact avram_b24_uniform_quadratic_energy_absorption_L1_error_vanish
    (P.restrict A) R Q M hM hQB hAbsorb
