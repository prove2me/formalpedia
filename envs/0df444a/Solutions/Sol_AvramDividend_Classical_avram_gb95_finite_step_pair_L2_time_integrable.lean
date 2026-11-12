-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb95_finite_step_pair_L2_time_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:11:22.498241+00:00
-- url     : https://prove2.me/submissions/dcd1b608-70a5-4275-a15e-6bc7d9591a87

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_avram_gb96_finite_step_pair_pointwise_L2
import Theorems.Thm_AvramDividend_Classical_avram_gb97_finite_step_pair_time_energy_L1
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
      Integrable (fun ω => K₁ t ω * K₂ t ω) P) ∧
    IntegrableOn (fun t => ∫ ω, (K₁ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, (K₂ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, K₁ t ω * K₂ t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by
  intro K₁ K₂
  have hpoint :=
    avram_gb96_finite_step_pair_pointwise_L2
      P T s₁ s₂ a₁ b₁ a₂ b₂ g₁ g₂ hg₁ hg₂ hB₁ hB₂
  have htime :=
    avram_gb97_finite_step_pair_time_energy_L1
      P T s₁ s₂ a₁ b₁ a₂ b₂ g₁ g₂ hg₁ hg₂ hB₁ hB₂ hpoint
  exact ⟨hpoint, htime.1, htime.2.1, htime.2.2⟩
