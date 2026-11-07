-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_integrated_mark_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:45:13.224985+00:00
-- url     : https://prove2.me/submissions/3eadb21d-1b5b-4313-a19b-5646d0b6e67d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! Integrate the quadratic collision bound for a random finite family of marks. -/
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (μ : Measure Ω) (S : Ω → Finset α) (q : Ω → α → ℝ)
    (hq0 : ∀ ω i, 0 ≤ q ω i) (hq1 : ∀ ω i, q ω i ≤ 1)
    (hE : Integrable (fun ω =>
      (∏ i ∈ S ω, q ω i) - (1 - ∑ i ∈ S ω, (1 - q ω i))) μ)
    (hC : Integrable (fun ω =>
      ((S ω).card : ℝ) * (((S ω).card : ℝ) - 1)) μ) :
    0 ≤ ∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂μ ∧
    2 * (∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂μ) ≤
      ∫ ω, (((S ω).card : ℝ) * (((S ω).card : ℝ) - 1)) ∂μ := by
  let E : Ω → ℝ := fun ω =>
    (∏ i ∈ S ω, q ω i) - (1 - ∑ i ∈ S ω, (1 - q ω i))
  let C : Ω → ℝ := fun ω =>
    ((S ω).card : ℝ) * (((S ω).card : ℝ) - 1)
  change Integrable E μ at hE
  change Integrable C μ at hC
  have hB (ω : Ω) : 0 ≤ E ω ∧ 2 * E ω ≤ C ω := by
    exact AvramDividend.Classical.avram_redux18_finite_mark_product_collision
      (S ω) (q ω) (hq0 ω) (hq1 ω)
  change 0 ≤ ∫ ω, E ω ∂μ ∧ 2 * (∫ ω, E ω ∂μ) ≤ ∫ ω, C ω ∂μ
  constructor
  · exact integral_nonneg (fun ω => (hB ω).1)
  · calc
      2 * (∫ ω, E ω ∂μ) = ∫ ω, 2 * E ω ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ ω, C ω ∂μ :=
        integral_mono (hE.const_mul 2) hC (fun ω => (hB ω).2)
