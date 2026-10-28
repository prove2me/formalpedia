-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_arbitrary_clock_kernel_future_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:45:15.460785+00:00
-- url     : https://prove2.me/submissions/6504d144-f8e2-467e-942d-3d75523de85d

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hKernel : ∀ a : ℝ≥0, Q {η : Θ | K a η} = discount a)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} =
      (P.prod Q) {z : Ω × Θ | K (τ z.1) z.2} *
        P (Y ⁻¹' B) := by
  have hF : Measurable (fun z : Ω × Θ => (τ z.1, z.2)) := (hτ.comp measurable_fst).prodMk measurable_snd
  have hs0 : MeasurableSet {z : Ω × Θ | K (τ z.1) z.2} := hF hK
  have hs : MeasurableSet {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} :=
    hs0.inter ((hY.comp measurable_fst) hB)
  have hslice : ∀ ω, Q (Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B}) =
      discount (τ ω) * B.indicator (fun _ => (1 : ℝ≥0∞)) (Y ω) := by
    intro ω
    by_cases hY' : Y ω ∈ B
    · have : Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} = {η | K (τ ω) η} := by
        ext η; simp [hY']
      rw [this, hKernel]; simp [hY']
    · have : Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} = ∅ := by
        ext η; simp [hY']
      rw [this, measure_empty]; simp [hY']
  have hslice0 : ∀ ω, Q (Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2}) = discount (τ ω) := by
    intro ω
    rw [← hKernel]; rfl
  rw [Measure.prod_apply hs, Measure.prod_apply hs0]
  simp_rw [hslice, hslice0]
  have hind : IndepFun (discount ∘ τ) (B.indicator (fun _ => (1 : ℝ≥0∞)) ∘ Y) P :=
    hInd.comp hd (measurable_const.indicator hB)
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hd.comp hτ)
    ((measurable_const.indicator hB).comp hY) hind
  simp only [Function.comp_def, Pi.mul_apply] at this
  rw [this]
  congr 1
  have hfun : (fun x => B.indicator (fun _ => (1 : ℝ≥0∞)) (Y x)) = (Y ⁻¹' B).indicator 1 := by
    ext x; by_cases h : Y x ∈ B <;> simp [h]
  rw [hfun, lintegral_indicator_one (hY hB)]