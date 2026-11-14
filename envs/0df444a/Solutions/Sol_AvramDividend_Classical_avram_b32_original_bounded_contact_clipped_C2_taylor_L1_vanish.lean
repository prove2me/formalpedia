-- Prove2me | solution 1 for AvramDividend.Classical.avram_b32_original_bounded_contact_clipped_C2_taylor_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:21.654194+00:00
-- url     : https://prove2.me/submissions/2ec05927-d70d-445e-b2aa-d89838b8bb8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_random_stopped_C2_taylor_uniform_expected_vanish
import Theorems.Thm_AvramDividend_Classical_avram_b30_original_random_clock_compact_square_energy_expected_card_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded count original random-stop compact cells have vanishing restricted physical C2 Taylor error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ (A : Set Ω) (S : ℕ → Finset ℕ)
      (s t : ℕ → ℕ → Ω → ℝ≥0),
      let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s m i ω)
      let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω - s m i ω) : ℝ) * X.c
      let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
        (w (z m ω i + g m ω i) -
          taylorWithinEval w 1
            (Set.uIcc (z m ω i) (z m ω i + g m ω i))
            (z m ω i) (z m ω i + g m ω i) -
          (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (s m i ω : WithTop ℝ≥0))) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (t m i ω : WithTop ℝ≥0))) →
      (∀ m, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
        z m ω i ∈ Icc a b ∧ z m ω i + g m ω i ∈ Icc a b ∧
        z m ω i ≠ z m ω i + g m ω i) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
          dist (z m ω i + g m ω i) (z m ω i) < δ) →
      (∀ m, AEStronglyMeasurable (fun ω => |R m ω|) (P.restrict A)) →
      ∀ L : ℕ, (∀ m, (S m).card ≤ L) →
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m, N ≤ m →
          IntegrableOn (fun ω => |R m ω|) A P ∧
          (∫ ω in A, |R m ω| ∂P) ≤ η := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A S s t
  dsimp only
  intro hs ht hBand hFine hRMeas L hCard η hη
  let K : ℝ := (L : ℝ) * (b - a) ^ 2 * (P A).toReal
  have hWidth : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have hProb : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hWidth) hProb
  have hEnergy (m : ℕ) :
      (∫ ω in A, ∑ i ∈ S m,
        (X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω : ℝ) - (s m i ω : ℝ)) * X.c) ^ 2 ∂P) ≤ K := by
    have hWeak : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s m i ω) ∈ Icc a b ∧
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s m i ω) +
        (X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω : ℝ) - (s m i ω : ℝ)) * X.c) ∈ Icc a b := by
      filter_upwards [hBand m] with ω hω i hi
      exact ⟨(hω i hi).1, (hω i hi).2.1⟩
    have hBound := (avram_b30_original_random_clock_compact_square_energy_expected_card_bound
      X x D a b hab A (S m) (s m) (t m)
      (fun i hi => hs m i hi) (fun i hi => ht m i hi) hWeak).2
    have hCardR : ((S m).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hCard m
    have hFactor : ((S m).card : ℝ) * (b - a) ^ 2 ≤
        (L : ℝ) * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hCardR hWidth
    exact le_trans hBound (mul_le_mul_of_nonneg_right hFactor hProb)
  exact avram_b29_original_random_stopped_C2_taylor_uniform_expected_vanish
    X x D hD C w hw a b ha hab hbcap A S s t hs ht hBand
    hFine hRMeas K hK hEnergy η hη
