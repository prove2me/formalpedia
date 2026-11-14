-- Prove2me | solution 1 for AvramDividend.Classical.avram_b31_original_single_clipped_C2_taylor_absolute_expectation_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:41:13.166469+00:00
-- url     : https://prove2.me/submissions/14fa63c7-d2ff-47f9-9f50-6e2f32b92a35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_random_clipped_C2_taylor_L1_automatic
import Theorems.Thm_AvramDividend_Classical_avram_b30_original_random_clock_compact_square_energy_expected_card_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single true random stopped compact C2 original physical cell has arbitrarily small expected Taylor error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Set Ω) (S : Finset ℕ)
        (s t : ℕ → Ω → ℝ≥0),
        let z : Ω → ℕ → ℝ := fun ω i =>
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) (s i ω)
        let g : Ω → ℕ → ℝ := fun ω i =>
          X.X (t i ω) ω - X.X (s i ω) ω -
            ((t i ω - s i ω) : ℝ) * X.c
        let R : Ω → ℝ := fun ω => ∑ i ∈ S,
          (w (z ω i + g ω i) -
            taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
              (z ω i) (z ω i + g ω i) -
            (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
        S.card ≤ 1 →
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (s i ω : WithTop ℝ≥0))) →
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (t i ω : WithTop ℝ≥0))) →
        (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
          z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
          z ω i ≠ z ω i + g ω i ∧
          dist (z ω i + g ω i) (z ω i) < δ) →
        AEStronglyMeasurable (fun ω => |R ω|) (P.restrict A) →
        IntegrableOn (fun ω => |R ω|) A P ∧
        (∫ ω in A, |R ω| ∂P) ≤ η * (P A).toReal := by
  classical
  intro η hη
  have hWidth : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have hKpos : 0 < (b - a) ^ 2 + 1 := by linarith
  have hEpos : 0 < η / ((b - a) ^ 2 + 1) :=
    div_pos hη hKpos
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_b28_original_random_clipped_C2_taylor_L1_automatic
      X x D hD C w hw a b ha hab hbcap
      (η / ((b - a) ^ 2 + 1)) hEpos
  refine ⟨δ, hδ, ?_⟩
  intro A S s t
  dsimp only
  intro hCard hs ht hBand hRMeas
  let z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s i ω)
  let g : Ω → ℕ → ℝ := fun ω i =>
    X.X (t i ω) ω - X.X (s i ω) ω -
      ((t i ω : ℝ) - (s i ω : ℝ)) * X.c
  let R : Ω → ℝ := fun ω => ∑ i ∈ S,
    (w (z ω i + g ω i) -
      taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
        (z ω i) (z ω i + g ω i) -
      (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
  let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
  have hWeak : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
      z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b := by
    filter_upwards [hBand] with ω hω i hi
    exact ⟨(hω i hi).1, (hω i hi).2.1⟩
  obtain ⟨hQI, hQBound⟩ :=
    avram_b30_original_random_clock_compact_square_energy_expected_card_bound
      X x D a b hab A S s t hs ht hWeak
  obtain ⟨hRI, hRBound⟩ :=
    hTaylor A S s t hs ht hBand hRMeas
  change IntegrableOn (fun ω => |R ω|) A P ∧
    (∫ ω in A, |R ω| ∂P) ≤ η * (P A).toReal
  refine ⟨hRI, ?_⟩
  have hCount : (S.card : ℝ) ≤ 1 := by exact_mod_cast hCard
  have hPn : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hFactor : (S.card : ℝ) * (b - a) ^ 2 ≤
      (b - a) ^ 2 := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hCount hWidth)
  have hEnergy : (∫ ω in A, Q ω ∂P) ≤
      (b - a) ^ 2 * (P A).toReal :=
    le_trans hQBound (mul_le_mul_of_nonneg_right hFactor hPn)
  calc
    (∫ ω in A, |R ω| ∂P) ≤
        (η / ((b - a) ^ 2 + 1)) * (∫ ω in A, Q ω ∂P) :=
      hRBound
    _ ≤ (η / ((b - a) ^ 2 + 1)) *
        ((b - a) ^ 2 * (P A).toReal) :=
      mul_le_mul_of_nonneg_left hEnergy hEpos.le
    _ ≤ η * (P A).toReal := by
      have hCoef : (η / ((b - a) ^ 2 + 1)) * (b - a) ^ 2 ≤ η := by
        calc
          _ ≤ (η / ((b - a) ^ 2 + 1)) *
              ((b - a) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hEpos.le
          _ = η := by field_simp
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hCoef hPn)
