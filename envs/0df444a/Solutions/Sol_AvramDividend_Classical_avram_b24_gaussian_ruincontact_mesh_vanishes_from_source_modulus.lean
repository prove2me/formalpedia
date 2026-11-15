-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_gaussian_ruincontact_mesh_vanishes_from_source_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:01:51.207879+00:00
-- url     : https://prove2.me/submissions/e970f5a2-0b4f-43cd-8d17-01212393359c

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
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
    (hMod : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => R (b k i) ω - R (a k i) ω))
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [hMod] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδpos, hRmod⟩ := hω (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := hGridSmall δ hδpos
  refine ⟨K, ?_⟩
  intro k hk
  have hCell (i : ℕ) (hi : i ∈ S k) :
      ‖R (b k i) ω - R (a k i) ω‖ ≤ ε / 2 :=
    hRmod (a k i) (b k i) (hOrdered k i hi)
      (hT k i hi) (hK k hk i hi)
  have hContact :=
    avram_b24_single_ruincontact_mesh_sum_norm_bound
      (S k) (a k) (b k) (σ ω)
      (fun i => R (b k i) ω - R (a k i) ω)
      (hSep k) (ε / 2) (by linarith) hCell
  have hStrict : ‖((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => R (b k i) ω - R (a k i) ω)‖ < ε := by
    linarith
  simpa only [dist_zero_right, Real.norm_eq_abs] using hStrict
