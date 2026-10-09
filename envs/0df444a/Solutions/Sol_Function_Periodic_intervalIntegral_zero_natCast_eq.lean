-- Prove2me | solution 1 for Function.Periodic.intervalIntegral_zero_natCast_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T18:45:46.247485+00:00
-- url     : https://prove2.me/submissions/2616719b-46bc-4774-a5e8-583e15251948

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic



theorem periodic_intervalIntegral_natCast_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Function.Periodic g 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..(k : ℝ), g x = (k : ℝ) • ∫ x in (0 : ℝ)..1, g x := by
  by_cases hint : IntervalIntegrable g MeasureTheory.volume 0 1
  · have hall : ∀ t₁ t₂, IntervalIntegrable g MeasureTheory.volume t₁ t₂ :=
      hg.intervalIntegrable₀ one_ne_zero hint
    have h := hg.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hall
    simpa [zero_add, Int.cast_natCast, ← Nat.cast_smul_eq_nsmul ℝ] using h
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hnk : ¬ IntervalIntegrable g MeasureTheory.volume 0 (k : ℝ) := by
      intro h
      apply hint
      refine h.mono_set ?_
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_right hk1
    rw [intervalIntegral.integral_undef hint, intervalIntegral.integral_undef hnk, smul_zero]

open Function.Periodic

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Function.Periodic g 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..(k : ℝ), g x = (k : ℝ) • ∫ x in (0 : ℝ)..1, g x :=
  periodic_intervalIntegral_natCast_aux hg k
