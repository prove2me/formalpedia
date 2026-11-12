-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb97_finite_step_pair_time_energy_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:26:16.993967+00:00
-- url     : https://prove2.me/submissions/621139ae-8ece-4a2e-b434-79d5fbc35c57

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb99_finite_step_abs_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb101_bounded_joint_integral_time_L1
import Theorems.Thm_AvramDividend_Classical_avram_gb102_finite_step_joint_stronglyMeasurable
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
    (∀ t : ℝ,
      Integrable (fun ω => (K₁ t ω) ^ 2) P ∧
      Integrable (fun ω => (K₂ t ω) ^ 2) P ∧
      Integrable (fun ω => K₁ t ω * K₂ t ω) P) →
    IntegrableOn (fun t => ∫ ω, (K₁ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, (K₂ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, K₁ t ω * K₂ t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by
  intro K₁ K₂ hpoint
  obtain ⟨B₁, hB₁0, hb₁⟩ := hB₁
  obtain ⟨B₂, hB₂0, hb₂⟩ := hB₂
  let C₁ : ℝ := (s₁.card : ℝ) * B₁
  let C₂ : ℝ := (s₂.card : ℝ) * B₂
  have hc₁ : 0 ≤ C₁ := mul_nonneg (Nat.cast_nonneg _) hB₁0
  have hc₂ : 0 ≤ C₂ := mul_nonneg (Nat.cast_nonneg _) hB₂0
  have hK₁ : StronglyMeasurable
      (fun z : ℝ × Ω => K₁ z.1 z.2) :=
    avram_gb102_finite_step_joint_stronglyMeasurable s₁ a₁ b₁ g₁ hg₁
  have hK₂ : StronglyMeasurable
      (fun z : ℝ × Ω => K₂ z.1 z.2) :=
    avram_gb102_finite_step_joint_stronglyMeasurable s₂ a₂ b₂ g₂ hg₂
  have hbK₁ (t : ℝ) (ω : Ω) : |K₁ t ω| ≤ C₁ :=
    avram_gb99_finite_step_abs_bound s₁ a₁ b₁ g₁ B₁ hB₁0 hb₁ t ω
  have hbK₂ (t : ℝ) (ω : Ω) : |K₂ t ω| ≤ C₂ :=
    avram_gb99_finite_step_abs_bound s₂ a₂ b₂ g₂ B₂ hB₂0 hb₂ t ω
  have hSqBound (f : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
      (hB : ∀ t ω, |f t ω| ≤ C) (t : ℝ) (ω : Ω) :
      ‖(f t ω) ^ 2‖ ≤ C ^ 2 := by
    have h := hB t ω
    have hs : |f t ω| ^ 2 ≤ C ^ 2 := by
      nlinarith [abs_nonneg (f t ω)]
    simpa [Real.norm_eq_abs, abs_pow] using hs
  refine ⟨?_, ?_, ?_⟩
  · exact avram_gb101_bounded_joint_integral_time_L1
      P T (fun t ω => (K₁ t ω) ^ 2) (hK₁.pow 2)
      (fun t => (hpoint t).1) (C₁ ^ 2) (sq_nonneg _)
      (hSqBound K₁ C₁ hc₁ hbK₁)
  · exact avram_gb101_bounded_joint_integral_time_L1
      P T (fun t ω => (K₂ t ω) ^ 2) (hK₂.pow 2)
      (fun t => (hpoint t).2.1) (C₂ ^ 2) (sq_nonneg _)
      (hSqBound K₂ C₂ hc₂ hbK₂)
  · apply avram_gb101_bounded_joint_integral_time_L1
      P T (fun t ω => K₁ t ω * K₂ t ω)
      (hK₁.mul hK₂) (fun t => (hpoint t).2.2)
      (C₁ * C₂) (mul_nonneg hc₁ hc₂)
    intro t ω
    simpa [Real.norm_eq_abs, abs_mul] using
      (mul_le_mul (hbK₁ t ω) (hbK₂ t ω) (abs_nonneg _) hc₁)
