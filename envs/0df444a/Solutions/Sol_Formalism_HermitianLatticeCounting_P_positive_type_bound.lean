-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.positive_type_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:39.667922+00:00
-- url     : https://prove2.me/submissions/5e3507a9-b634-41ca-857e-a99e5407b07d

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

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
theorem _root_.solution : PosTypeBound := by
  classical
  intro G _ e he x
  have h1 : 0 ≤ e 1 := by
    have := he {1} (fun _ => 1)
    simpa using this
  have h1re : 0 ≤ (e 1).re := (Complex.le_def.mp h1).1
  have h1im : (e 1).im = 0 := ((Complex.le_def.mp h1).2).symm
  by_cases hx : x = 1
  · subst hx
    rw [← Complex.re_add_im (e 1), h1im]
    simp [abs_of_nonneg h1re]
  have hpair : ∀ t : ℂ, 0 ≤ e 1 + t * e x + star t * e x⁻¹ + star t * t * e 1 := by
    intro t
    have := he {1, x} (fun y => if y = 1 then 1 else t)
    rw [Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx)] at this
    simp only [if_true, if_neg hx, inv_one, one_mul, mul_one, star_one, inv_mul_cancel] at this
    convert this using 1
    ring
  have ha := hpair 1
  have hb := hpair Complex.I
  rw [Complex.le_def] at ha hb
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.zero_re,
    Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, star_one,
    Complex.star_def, Complex.conj_I, Complex.neg_re, Complex.neg_im] at ha hb
  have him : (e x⁻¹).im = -(e x).im := by linarith [ha.2]
  have hre : (e x⁻¹).re = (e x).re := by linarith [hb.2]
  by_cases h0 : e x = 0
  · rw [h0, norm_zero]; exact h1re
  have hn : 0 < ‖e x‖ := norm_pos_iff.mpr h0
  have hc := hpair (-(star (e x)) / (‖e x‖ : ℂ))
  rw [Complex.le_def] at hc
  have hsq : (e x).re * (e x).re + (e x).im * (e x).im = ‖e x‖ * ‖e x‖ := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; ring
  have hinv : e x⁻¹ = star (e x) := by
    apply Complex.ext <;> simp [hre, him]
  have hval : e 1 + (-(star (e x)) / (‖e x‖ : ℂ)) * e x
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * e x⁻¹
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * (-(star (e x)) / (‖e x‖ : ℂ)) * e 1
      = 2 * e 1 - 2 * (‖e x‖ : ℂ) := by
    have hne : (‖e x‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm : star (e x) * e x = (‖e x‖ : ℂ) * (‖e x‖ : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; ring
    rw [hinv]
    simp only [star_div₀, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.star_def] at hm
    field_simp
    linear_combination (-2 * (‖e x‖ : ℂ) + e 1) * hm
  rw [hval] at hc
  have := hc.1
  simp at this
  linarith
end Formalism.HermitianLatticeCounting.P
