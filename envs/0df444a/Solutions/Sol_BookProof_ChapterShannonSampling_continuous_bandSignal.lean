-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.continuous_bandSignal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:36.163461+00:00
-- url     : https://prove2.me/submissions/295a059c-d87b-4281-92b5-70e7b84ec7f6

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.continuous_bandSignal
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : AddCircle T → ℂ)
    (hF : IntegrableOn (fun ξ : ℝ => F ξ) (Ioc (-(T / 2)) (-(T / 2) + T)) volume) :
    Continuous (bandSignal (T := T) F) := by

  have hle : -(T / 2) ≤ -(T / 2) + T := by linarith [hT.out]
  have hrepr : (bandSignal (T := T) F)
      = fun x : ℝ => ∫ ξ in (-(T / 2))..(-(T / 2) + T), Complex.exp (2 * π * I * x * ξ) * F ξ := by
    funext x
    rw [bandSignal, half_add_period]
  rw [hrepr]
  simp_rw [intervalIntegral.integral_of_le hle]
  refine continuous_of_dominated
    (F := fun (x : ℝ) (ξ : ℝ) => Complex.exp (2 * π * I * x * ξ) * F ξ)
    (bound := fun ξ => ‖F ξ‖) ?_ ?_ ?_ ?_
  · intro x
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  · intro x
    filter_upwards with ξ
    rw [norm_mul]
    have hphase : ‖Complex.exp (2 * (π : ℂ) * I * (x : ℂ) * (ξ : ℂ))‖ = 1 := by
      rw [show (2 * (π : ℂ) * I * x * ξ) = ((2 * π * x * ξ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [hphase, one_mul]
  · exact hF.norm
  · filter_upwards with ξ
    exact (Complex.continuous_exp.comp (by fun_prop)).mul continuous_const
