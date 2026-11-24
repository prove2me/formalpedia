-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.resolution_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:57.958115+00:00
-- url     : https://prove2.me/submissions/d42be8d9-0d04-4f39-bbd8-a5bba4b2627b

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_resolution_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ResolutionNorm := by
  intro Ω T _ μ _ _ v c M A hM hres hc hA
  have key : ∀ (x y : T) (t : ℝ), 0 < t →
      ‖inner ℂ x (A y)‖ ≤ M * ((t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t) / 2) := by
    intro x y t ht
    obtain ⟨ix, ex⟩ := resolution_sq μ v hres x
    obtain ⟨iy, ey⟩ := resolution_sq μ v hres y
    rw [hA x y]
    have hg : Integrable (fun k => M * ((t * ‖inner ℂ x (v k)‖ ^ 2 + ‖inner ℂ y (v k)‖ ^ 2 / t) / 2)) μ :=
      (((ix.const_mul t).add (iy.div_const t)).div_const 2).const_mul M
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inner_symm (v k) y]
      set p := ‖inner ℂ x (v k)‖
      set q := ‖inner ℂ y (v k)‖
      have hp : 0 ≤ p := norm_nonneg _
      have hq : 0 ≤ q := norm_nonneg _
      have h1 : p * q ≤ (t * p ^ 2 + q ^ 2 / t) / 2 := by
        have h0 : 0 ≤ (t * p - q) ^ 2 / t := by positivity
        have e : (t * p - q) ^ 2 / t = t * p ^ 2 - 2 * (p * q) + q ^ 2 / t := by
          field_simp; ring
        linarith
      exact mul_le_mul (hc k) h1 (by positivity) hM
    · apply le_of_eq
      rw [integral_const_mul, integral_div, integral_add (ix.const_mul t) (iy.div_const t),
        integral_const_mul, integral_div, ex, ey]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro y
  by_cases hy : y = 0
  · subst hy; simp
  by_cases hAy : A y = 0
  · rw [hAy, norm_zero]; positivity
  have ha : 0 < ‖A y‖ := norm_pos_iff.mpr hAy
  have hb : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := key (A y) y (‖y‖ / ‖A y‖) (by positivity)
  rw [inner_self_eq_norm_sq_to_K] at h
  have e1 : ‖((‖A y‖ : ℂ)) ^ 2‖ = ‖A y‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, norm_norm]
  have e2 : (‖y‖ / ‖A y‖ * ‖A y‖ ^ 2 + ‖y‖ ^ 2 / (‖y‖ / ‖A y‖)) / 2 = ‖A y‖ * ‖y‖ := by
    field_simp; ring
  erw [e1] at h
  rw [e2] at h
  have : ‖A y‖ * ‖A y‖ ≤ ‖A y‖ * (M * ‖y‖) := by nlinarith
  exact le_of_mul_le_mul_left this ha
end Formalism.HermitianLatticeCounting.P
