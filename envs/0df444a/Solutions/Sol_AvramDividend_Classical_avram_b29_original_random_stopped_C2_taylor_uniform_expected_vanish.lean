-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_original_random_stopped_C2_taylor_uniform_expected_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:13:35.520812+00:00
-- url     : https://prove2.me/submissions/ec8454d6-1c7a-4bef-b30f-23d455c27eab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_random_clipped_C2_taylor_L1_automatic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original random stopped compact C2 Taylor meshes have vanishing restricted L1 error under uniform energy. -/
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
      let Q : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m, (g m ω i) ^ 2
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
      ∀ K : ℝ, 0 ≤ K →
        (∀ m, (∫ ω in A, Q m ω ∂P) ≤ K) →
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m, N ≤ m →
          IntegrableOn (fun ω => |R m ω|) A P ∧
          (∫ ω in A, |R m ω| ∂P) ≤ η := by
  classical
  intro A S s t
  dsimp only
  intro hs ht hBand hFine hRMeas K hK hEnergy η hη
  have hKpos : 0 < K + 1 := by linarith
  have hEpos : 0 < η / (K + 1) := div_pos hη hKpos
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_b28_original_random_clipped_C2_taylor_L1_automatic
      X x D hD C w hw a b ha hab hbcap (η / (K + 1)) hEpos
  obtain ⟨N, hN⟩ := hFine δ hδ
  refine ⟨N, ?_⟩
  intro m hm
  let z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s m i ω)
  let g : Ω → ℕ → ℝ := fun ω i =>
    X.X (t m i ω) ω - X.X (s m i ω) ω -
      ((t m i ω - s m i ω) : ℝ) * X.c
  let Q : Ω → ℝ := fun ω => ∑ i ∈ S m, (g ω i) ^ 2
  let R : Ω → ℝ := fun ω => ∑ i ∈ S m,
    (w (z ω i + g ω i) -
      taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
        (z ω i) (z ω i + g ω i) -
      (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
  have hBandFull : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
      z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
      z ω i ≠ z ω i + g ω i ∧
      dist (z ω i + g ω i) (z ω i) < δ := by
    filter_upwards [hBand m, hN m hm] with ω hB hF i hi
    rcases hB i hi with ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, hF i hi⟩
  obtain ⟨hRint, hBound⟩ :=
    hTaylor A (S m) (s m) (t m)
      (fun i hi => hs m i hi) (fun i hi => ht m i hi)
      hBandFull (hRMeas m)
  change IntegrableOn (fun ω => |R ω|) A P ∧
    (∫ ω in A, |R ω| ∂P) ≤ η
  refine ⟨hRint, ?_⟩
  calc
    (∫ ω in A, |R ω| ∂P) ≤
        (η / (K + 1)) * (∫ ω in A, Q ω ∂P) := hBound
    _ ≤ (η / (K + 1)) * K :=
      mul_le_mul_of_nonneg_left (hEnergy m) hEpos.le
    _ ≤ η := by
      calc
        (η / (K + 1)) * K ≤
            (η / (K + 1)) * (K + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hEpos.le
        _ = η := by field_simp
