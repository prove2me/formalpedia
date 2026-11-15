-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:01:59.53109+00:00
-- url     : https://prove2.me/submissions/09d569b3-423b-4261-b48c-fd1c2c758850

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (T : ℝ≥0)
    (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ≥0)
    (WG : ℕ → ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hWeights : ∀ k i, i ∈ S k → ∀ ω, ‖WG k i ω‖ ≤ L)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
    (hMod : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [hMod] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hDen : 0 < 2 * (L + 1) := by nlinarith
  have hSmall : 0 < ε / (2 * (L + 1)) := div_pos hε hDen
  obtain ⟨δ, hδpos, hRmod⟩ := hω _ hSmall
  obtain ⟨K, hK⟩ := hGridSmall δ hδpos
  refine ⟨K, ?_⟩
  intro k hk
  have hRatio : L / (L + 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have hCell (i : ℕ) (hi : i ∈ S k) :
      ‖WG k i ω * (R (b k i) ω - R (a k i) ω)‖ ≤ ε / 2 := by
    have hW := hWeights k i hi ω
    have hR := hRmod (a k i) (b k i)
      (hOrdered k i hi) (hT k i hi) (hK k hk i hi)
    rw [norm_mul]
    calc
      ‖WG k i ω‖ * ‖R (b k i) ω - R (a k i) ω‖ ≤
          L * (ε / (2 * (L + 1))) :=
        mul_le_mul hW hR (norm_nonneg _) hL
      _ = (ε / 2) * (L / (L + 1)) := by field_simp
      _ ≤ (ε / 2) * 1 :=
        mul_le_mul_of_nonneg_left hRatio (by linarith)
      _ = ε / 2 := by ring
  have hContact :=
    avram_b24_single_ruincontact_mesh_sum_norm_bound
      (S k) (a k) (b k) (σ ω)
      (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))
      (hSep k) (ε / 2) (by linarith) hCell
  have hStrict : ‖((S k).filter
      (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))‖ < ε := by
    linarith
  simpa only [dist_zero_right, Real.norm_eq_abs] using hStrict
