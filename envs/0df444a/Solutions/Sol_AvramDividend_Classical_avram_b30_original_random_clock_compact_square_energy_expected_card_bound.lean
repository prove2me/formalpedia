-- Prove2me | solution 1 for AvramDividend.Classical.avram_b30_original_random_clock_compact_square_energy_expected_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:16.199255+00:00
-- url     : https://prove2.me/submissions/9f24dd68-3129-43c0-8c9f-6dbe871390fb

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite random stopped original physical compact mesh quadratic energy obeys a card band expectation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ)
      (s t : ℕ → Ω → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i ω)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (s i ω : WithTop ℝ≥0))) →
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (t i ω : WithTop ℝ≥0))) →
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      IntegrableOn Q A P ∧
        (∫ ω in A, Q ω ∂P) ≤
          ((S.card : ℝ) * (b - a) ^ 2) * (P A).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A S s t
  dsimp only
  intro hs ht hBand
  let z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s i ω)
  let g : Ω → ℕ → ℝ := fun ω i =>
    X.X (t i ω) ω - X.X (s i ω) ω -
      ((t i ω : ℝ) - (s i ω : ℝ)) * X.c
  let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
  have hQint : IntegrableOn Q A P :=
    avram_b27_original_random_stopped_compact_mesh_energy_L1
      X x D a b hab A S s t hs ht hBand
  have hPoint : ∀ᵐ ω ∂(P.restrict A),
      Q ω ≤ (S.card : ℝ) * (b - a) ^ 2 := by
    filter_upwards [hBand] with ω hω
    calc
      Q ω ≤ ∑ i ∈ S, (b - a) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hz, hzg⟩ := hω i hi
        rcases Set.mem_Icc.mp hz with ⟨hza, hzb⟩
        rcases Set.mem_Icc.mp hzg with ⟨hga, hgb⟩
        have hMinus : 0 ≤ (b - a) - g ω i := by
          dsimp [z, g] at hza hzb hga hgb ⊢
          linarith
        have hPlus : 0 ≤ (b - a) + g ω i := by
          dsimp [z, g] at hza hzb hga hgb ⊢
          linarith
        nlinarith [mul_nonneg hMinus hPlus]
      _ = (S.card : ℝ) * (b - a) ^ 2 := by simp
  have hMean := integral_mono_ae hQint
    (integrable_const ((S.card : ℝ) * (b - a) ^ 2)) hPoint
  refine ⟨hQint, ?_⟩
  change (∫ ω in A, Q ω ∂P) ≤
    ((S.card : ℝ) * (b - a) ^ 2) * (P A).toReal
  calc
    (∫ ω in A, Q ω ∂P) ≤
        (P A).toReal * ((S.card : ℝ) * (b - a) ^ 2) := by
      simpa [integral_const, Measure.real] using hMean
    _ = _ := mul_comm _ _
