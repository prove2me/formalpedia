-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:17:49.83706+00:00
-- url     : https://prove2.me/submissions/707bb48e-b9d9-4e8f-81d4-d3d61e5ed519

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0) :
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
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      (∫ ω in A, |R k ω| ∂P) ≤
        ε * (∫ ω in A, Q k ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro z g R Q hBand hSmall hQM hRM ε hε
  have hIcc : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hy.2) hbcap⟩
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
      X x D hD C w hw a b ha hab hbcap hIcc ε hε
  obtain ⟨K, hK⟩ := hSmall δ hδ
  refine ⟨K, ?_⟩
  intro k hk
  have hQint : IntegrableOn (Q k) A P := by
    have hFinite : P A < ⊤ := measure_lt_top P A
    apply IntegrableOn.of_bound hFinite (hQM k)
      ((S k).card * (b - a) ^ 2)
    filter_upwards [hBand k] with ω hw
    have hnonneg : 0 ≤ Q k ω := by
      dsimp [Q]
      apply Finset.sum_nonneg
      intro i hi
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      Q k ω ≤ ∑ i ∈ S k, (b - a) ^ 2 := by
        dsimp [Q]
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hz, hzg, _⟩ := hw i hi
        rcases hz with ⟨hza, hzb⟩
        rcases hzg with ⟨hga, hgb⟩
        have hm : 0 ≤ (b - a) - g k ω i := by linarith
        have hp : 0 ≤ (b - a) + g k ω i := by linarith
        nlinarith [mul_nonneg hm hp]
      _ = ((S k).card : ℝ) * (b - a) ^ 2 := by simp
  have hMod : ∀ᵐ ω ∂(P.restrict A), |R k ω| ≤ ε * Q k ω := by
    filter_upwards [hBand k, hK k hk] with ω hb hs
    let f : ℕ → ℝ := fun i =>
      w (z k ω i + g k ω i) -
        taylorWithinEval w 1 (Set.uIcc (z k ω i) (z k ω i + g k ω i))
          (z k ω i) (z k ω i + g k ω i) -
        (iteratedDeriv 2 w (z k ω i) * (g k ω i)^2) / 2
    have hp (i : ℕ) (hi : i ∈ S k) : |f i| ≤ ε * (g k ω i)^2 := by
      obtain ⟨hz, hzg, hne⟩ := hb i hi
      have ht := hTaylor ω (s k i) (z k ω i + g k ω i)
      dsimp only at ht
      simpa [f, z, add_sub_cancel_left] using ht hz hzg hne (hs i hi)
    calc
      |R k ω| = |∑ i ∈ S k, f i| := rfl
      _ ≤ ∑ i ∈ S k, |f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S k, ε * (g k ω i)^2 := Finset.sum_le_sum hp
      _ = ε * Q k ω := by simp [Q, Finset.mul_sum]
  have hRint : IntegrableOn (fun ω => |R k ω|) A P :=
    Integrable.mono' (hQint.const_mul ε) (hRM k) (by
      filter_upwards [hMod] with ω hω
      simpa [Real.norm_eq_abs] using hω)
  have hI := integral_mono_ae hRint (hQint.const_mul ε) hMod
  simpa only [integral_const_mul] using hI
