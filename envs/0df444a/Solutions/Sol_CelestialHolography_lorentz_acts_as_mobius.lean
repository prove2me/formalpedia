-- Prove2me | solution 1 for CelestialHolography.lorentz_acts_as_mobius
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:46:56.303977+00:00
-- url     : https://prove2.me/submissions/7aef08c3-11bc-47e7-9c39-5031d6513600

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CelestialHolography in
theorem lam_eq_199673ff (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    lorentzOfSL2C M x = fromHermitian
      (!![M 0 0, M 0 1; M 1 0, M 1 1] * toHermitian x *
        !![star (M 0 0), star (M 1 0); star (M 0 1), star (M 1 1)]) := by
  unfold lorentzOfSL2C
  congr 3
  · exact Matrix.eta_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ)
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

open CelestialHolography in
theorem part1_199673ff (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    minkowskiNormSq (lorentzOfSL2C M x) = minkowskiNormSq x := by
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  rw [lam_eq_199673ff]
  generalize M 0 0 = a at *
  generalize M 0 1 = b at *
  generalize M 1 0 = c at *
  generalize M 1 1 = d at *
  have hr := congrArg Complex.re hdet
  have hi := congrArg Complex.im hdet
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im] at hr hi
  simp only [minkowskiNormSq, fromHermitian, toHermitian, 
    Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val, Fin.isValue,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  linear_combination (-(x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2) *
    ((a.re * d.re - a.im * d.im - (b.re * c.re - b.im * c.im) + 1) * hr +
      (a.re * d.im + a.im * d.re - (b.re * c.im + b.im * c.re)) * hi)

open CelestialHolography in
theorem part2_199673ff (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hz : M 1 0 * z + M 1 1 ≠ 0) :
    lorentzOfSL2C M (nullVector z) =
      Complex.normSq (M 1 0 * z + M 1 1) • nullVector (mobius M z) := by
  rw [lam_eq_199673ff]
  unfold mobius
  generalize M 0 0 = a at *
  generalize M 0 1 = b at *
  generalize M 1 0 = c at *
  generalize M 1 1 = d at *
  set w := (a * z + b) / (c * z + d) with hw
  have hb : b = w * (c * z + d) - a * z := by
    rw [hw, div_mul_cancel₀ _ hz]; ring
  clear_value w
  subst hb
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  funext i
  fin_cases i <;>
  simp only [nullVector, fromHermitian, toHermitian, 
    Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val, Fin.isValue, Pi.smul_apply, smul_eq_mul,
    Complex.div_re, Complex.div_im, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.one_re, Complex.one_im, Complex.div_ofNat_re] <;>
  field_simp <;>
  ring

open CelestialHolography in
theorem solution (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (∀ x : Fin 4 → ℝ, minkowskiNormSq (lorentzOfSL2C M x) = minkowskiNormSq x) ∧
    ∀ z : ℂ, M 1 0 * z + M 1 1 ≠ 0 →
      lorentzOfSL2C M (nullVector z) =
        Complex.normSq (M 1 0 * z + M 1 1) • nullVector (mobius M z) := by
  exact ⟨fun x => part1_199673ff M x, fun z hz => part2_199673ff M z hz⟩
