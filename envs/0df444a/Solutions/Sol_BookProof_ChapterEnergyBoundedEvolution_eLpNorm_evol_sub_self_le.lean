-- Prove2me | solution 1 for BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:02:36.655703+00:00
-- url     : https://prove2.me/submissions/9fa6eefb-160d-4be2-b859-5cb3ff01f496

import Definitions.Def_ChapterEnergyBandDecomposition
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
-- Generated from ChapterEnergyBoundedEvolution.lean — theorem BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le
open BookProof.ChapterEnergyBoundedEvolution



open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}
theorem solution {Emax : ℝ} (h : EnergyLimited E μ Emax f) (t : ℝ) :
    eLpNorm (evol E t f - f) 2 μ ≤ ENNReal.ofReal (|t| * Emax) * eLpNorm f 2 μ := by
  have hpt : ∀ x, ‖evol E t f x - f x‖ = ‖Complex.exp (Complex.I * ((-(t * E x) : ℝ) : ℂ)) - 1‖ * ‖f x‖ := by
    intro x
    unfold evol
    rw [← norm_mul, sub_mul, one_mul]
    congr 2
    push_cast; ring_nf
  rcases le_or_gt 0 Emax with hE | hE
  · have hbound : ∀ᵐ x ∂μ, ‖(evol E t f - f) x‖ ≤ ‖((|t| * Emax : ℝ) : ℂ) • f x‖ := by
      filter_upwards [h] with x hx
      rw [Pi.sub_apply, hpt, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      by_cases hfx : f x = 0
      · simp [hfx]
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc ‖Complex.exp (Complex.I * ((-(t * E x) : ℝ) : ℂ)) - 1‖ ≤ ‖(-(t * E x) : ℝ)‖ :=
              Real.norm_exp_I_mul_ofReal_sub_one_le
          _ = |t| * |E x| := by rw [Real.norm_eq_abs, abs_neg, abs_mul]
          _ ≤ |t| * Emax := mul_le_mul_of_nonneg_left (hx hfx) (abs_nonneg t)
    calc eLpNorm (evol E t f - f) 2 μ ≤ eLpNorm (fun x => ((|t| * Emax : ℝ) : ℂ) • f x) 2 μ :=
          eLpNorm_mono_ae hbound
      _ = ENNReal.ofReal (|t| * Emax) * eLpNorm f 2 μ := by
          rw [show (fun x => ((|t| * Emax : ℝ) : ℂ) • f x) = ((|t| * Emax : ℝ) : ℂ) • f from rfl,
            eLpNorm_const_smul]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · have hz : ∀ᵐ x ∂μ, (evol E t f - f) x = 0 := by
      filter_upwards [h] with x hx
      by_cases hfx : f x = 0
      · simp [evol, hfx]
      · exact absurd (hx hfx) (by intro h'; linarith [abs_nonneg (E x)])
    have hz' : (evol E t f - f) =ᵐ[μ] 0 := by
      filter_upwards [hz] with x hx
      simpa using hx
    rw [eLpNorm_congr_ae hz']
    simp
