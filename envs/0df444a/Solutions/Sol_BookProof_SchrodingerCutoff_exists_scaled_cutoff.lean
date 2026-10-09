-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.exists_scaled_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:44.643988+00:00
-- url     : https://prove2.me/submissions/2c712d8b-400d-438b-a5a1-5f032d6b9f56

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.exists_scaled_cutoff
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_continuous
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_differentiable
import Theorems.Thm_BookProof_SchrodingerCutoff_deriv_chi_continuous
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_eq_one_of_abs_le_one
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_eq_zero
import Theorems.Thm_BookProof_SchrodingerCutoff_deriv_chi_eq_zero
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution {C R : ℝ} (hC : ∀ y, |deriv chi y| ≤ C) (hR : 0 < R) :
    ∃ w wd : ℝ → ℝ, (∀ x, HasDerivAt w (wd x) x) ∧ Continuous w ∧ Continuous wd ∧
      (∀ x : ℝ, 2 * R < |x| → w x = 0) ∧ (∀ x : ℝ, 2 * R < |x| → wd x = 0) ∧
      (∀ x : ℝ, |x| ≤ R → w x = 1) ∧ (∀ x, |wd x| ≤ C / R) := by

  have hRi : (0 : ℝ) < R⁻¹ := by positivity
  refine ⟨fun x => chi (R⁻¹ * x), fun x => deriv chi (R⁻¹ * x) * R⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hlin : HasDerivAt (fun y : ℝ => R⁻¹ * y) R⁻¹ x := by
      simpa using (hasDerivAt_id x).const_mul R⁻¹
    simpa [Function.comp_def] using
      ((chi_differentiable (R⁻¹ * x)).hasDerivAt.comp x hlin)
  · exact chi_continuous.comp (by fun_prop)
  · exact (deriv_chi_continuous.comp (by fun_prop)).mul continuous_const
  · intro x hx
    refine chi_eq_zero ?_
    rw [abs_mul, abs_of_pos hRi]
    have h2 : R⁻¹ * (2 * R) ≤ R⁻¹ * |x| := by nlinarith
    calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
      _ ≤ R⁻¹ * |x| := h2
  · intro x hx
    have hgt : (2 : ℝ) < |R⁻¹ * x| := by
      rw [abs_mul, abs_of_pos hRi]
      have h2 : R⁻¹ * (2 * R) < R⁻¹ * |x| := by nlinarith
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ < R⁻¹ * |x| := h2
    simp [deriv_chi_eq_zero hgt]
  · intro x hx
    refine chi_eq_one_of_abs_le_one ?_
    rw [abs_mul, abs_of_pos hRi]
    have h2 : R⁻¹ * |x| ≤ R⁻¹ * R := by nlinarith
    calc R⁻¹ * |x| ≤ R⁻¹ * R := h2
      _ = 1 := by field_simp
  · intro x
    rw [abs_mul, abs_of_pos hRi]
    have := hC (R⁻¹ * x)
    rw [div_eq_inv_mul]
    nlinarith [abs_nonneg (deriv chi (R⁻¹ * x))]
