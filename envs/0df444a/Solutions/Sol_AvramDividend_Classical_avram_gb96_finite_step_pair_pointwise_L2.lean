-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb96_finite_step_pair_pointwise_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:21:34.089402+00:00
-- url     : https://prove2.me/submissions/e52702da-29ae-4e10-ab2d-5c759f40bdb1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb98_finite_step_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_gb99_finite_step_abs_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb100_bounded_stronglyMeasurable_pair_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℝ) (s₁ s₂ : Finset ℕ)
    (a₁ b₁ a₂ b₂ : ℕ → ℝ) (g₁ g₂ : ℕ → Ω → ℝ)
    (hg₁ : ∀ i ∈ s₁, StronglyMeasurable (g₁ i))
    (hg₂ : ∀ i ∈ s₂, StronglyMeasurable (g₂ i))
    (hB₁ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ s₁, ∀ ω, |g₁ i ω| ≤ B)
    (hB₂ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ s₂, ∀ ω, |g₂ i ω| ≤ B) :
    let K₁ : ℝ → Ω → ℝ := fun t ω =>
      s₁.sum (fun i => if a₁ i ≤ t ∧ t < b₁ i then g₁ i ω else 0)
    let K₂ : ℝ → Ω → ℝ := fun t ω =>
      s₂.sum (fun i => if a₂ i ≤ t ∧ t < b₂ i then g₂ i ω else 0)
    ∀ t : ℝ,
      Integrable (fun ω => (K₁ t ω) ^ 2) P ∧
      Integrable (fun ω => (K₂ t ω) ^ 2) P ∧
      Integrable (fun ω => K₁ t ω * K₂ t ω) P := by
  intro K₁ K₂ t
  obtain ⟨B₁, hB₁0, hb₁⟩ := hB₁
  obtain ⟨B₂, hB₂0, hb₂⟩ := hB₂
  have hc₁ : 0 ≤ (s₁.card : ℝ) * B₁ := mul_nonneg (Nat.cast_nonneg _) hB₁0
  have hc₂ : 0 ≤ (s₂.card : ℝ) * B₂ := mul_nonneg (Nat.cast_nonneg _) hB₂0
  exact avram_gb100_bounded_stronglyMeasurable_pair_L2
    P (K₁ t) (K₂ t)
    (avram_gb98_finite_step_stronglyMeasurable s₁ a₁ b₁ g₁ hg₁ t)
    (avram_gb98_finite_step_stronglyMeasurable s₂ a₂ b₂ g₂ hg₂ t)
    ((s₁.card : ℝ) * B₁) ((s₂.card : ℝ) * B₂) hc₁ hc₂
    (fun ω => avram_gb99_finite_step_abs_bound
      s₁ a₁ b₁ g₁ B₁ hB₁0 hb₁ t ω)
    (fun ω => avram_gb99_finite_step_abs_bound
      s₂ a₂ b₂ g₂ B₂ hB₂0 hb₂ t ω)
