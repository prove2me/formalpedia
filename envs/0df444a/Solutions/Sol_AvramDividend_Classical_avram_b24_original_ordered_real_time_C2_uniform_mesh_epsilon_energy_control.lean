-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_ordered_real_time_C2_uniform_mesh_epsilon_energy_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:25:37.917344+00:00
-- url     : https://prove2.me/submissions/1bc12804-ab08-42f2-bc69-2371e9a433ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_preleft_C2_compact_taylor_L1_automatic
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
    (hOrdered : ∀ k i, i ∈ S k → s k i ≤ t k i) :
    let z : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s k i)
    let g : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      X.X (t k i) ω - X.X (s k i) ω -
        ((t k i : ℝ) - (s k i : ℝ)) * X.c
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
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      (∫ ω in A, |R k ω| ∂P) ≤
        ε * (∫ ω in A, Q k ω ∂P) := by
  intro z g R Q hBand hSmall hQM hRM ε hε
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_b24_original_preleft_C2_compact_taylor_L1_automatic
      X x D hD C w hw a b ha hab hbcap ε hε
  obtain ⟨K, hK⟩ := hSmall δ hδ
  refine ⟨K, ?_⟩
  intro k hk
  have hb := hBand k
  have hs := hK k hk
  have hBoth : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
      z k ω i ∈ Icc a b ∧ z k ω i + g k ω i ∈ Icc a b ∧
      z k ω i ≠ z k ω i + g k ω i ∧
      dist (z k ω i + g k ω i) (z k ω i) < δ := by
    filter_upwards [hb, hs] with ω hbw hsw
    intro i hi
    exact ⟨(hbw i hi).1, (hbw i hi).2.1,
      (hbw i hi).2.2, hsw i hi⟩
  exact (hTaylor A (S k) (s k) (t k) hBoth
    (hQM k) (hRM k)).2
