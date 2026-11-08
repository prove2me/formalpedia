-- Prove2me | solution 1 for CalendarDependentRM.lemma_J_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:57:08.879751+00:00
-- url     : https://prove2.me/submissions/fb1d0130-fa72-4e1a-86b8-8b1510e62228

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : ∀ᵐ ω ∂P, Z ω = 0 ∨ Z ω = 1) {μ : ℝ}
    (hμ : ∫ ω, Z ω ∂P = μ) {lamb : ℝ} (hl : lamb ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, Real.exp (lamb * (Z ω - μ)) ∂P ≤ Real.exp (μ * lamb ^ 2) := by
  obtain ⟨hl0, hl1⟩ := hl
  have hint : Integrable Z P := by
    refine Integrable.of_bound hZm.aestronglyMeasurable 1 ?_
    filter_upwards [hZ] with ω h
    rcases h with h | h <;> simp [h]
  have hμ0 : 0 ≤ μ := by
    rw [← hμ]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hZ] with ω h
    rcases h with h | h <;> simp [h]
  have hae : (fun ω => Real.exp (lamb * (Z ω - μ))) =ᵐ[P]
      fun ω => Real.exp (-(lamb * μ)) * (1 + (Real.exp lamb - 1) * Z ω) := by
    filter_upwards [hZ] with ω h
    rcases h with h | h
    · rw [h, show lamb * (0 - μ) = -(lamb * μ) by ring]
      ring
    · rw [h, show lamb * (1 - μ) = -(lamb * μ) + lamb by ring, Real.exp_add]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_add (integrable_const _) (hint.const_mul _), integral_const_mul, hμ,
    integral_const, probReal_univ, one_smul]
  have h1 : 1 + (Real.exp lamb - 1) * μ ≤ Real.exp ((Real.exp lamb - 1) * μ) := by
    linarith [Real.add_one_le_exp ((Real.exp lamb - 1) * μ)]
  have h2 : Real.exp lamb - 1 ≤ lamb + lamb ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := lamb) (by rw [abs_of_nonneg hl0]; exact hl1)
    have := le_abs_self (Real.exp lamb - 1 - lamb)
    linarith
  have h3 : Real.exp ((Real.exp lamb - 1) * μ) ≤ Real.exp ((lamb + lamb ^ 2) * μ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hμ0)
  calc Real.exp (-(lamb * μ)) * (1 + (Real.exp lamb - 1) * μ)
      ≤ Real.exp (-(lamb * μ)) * Real.exp ((lamb + lamb ^ 2) * μ) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (Real.exp_pos _).le
    _ = Real.exp (μ * lamb ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
