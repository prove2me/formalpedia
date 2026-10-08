-- Prove2me | solution 2 for ConnesGreen.supported_mellin_norm_sq_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:23:51.683983+00:00
-- url     : https://prove2.me/submissions/80c90747-e9ee-408c-af2e-b6b1efb43f41

import Theorems.Thm_ConnesGreen_norm_integral_sq_le_mass_integral_norm_sq
import Definitions.Def_ConnesRZ_weil_defs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ Set
noncomputable section

theorem solution (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : IsTest g ∧ tsupport g ⊆ Ioo (-T) T) (z : ℂ) :
    ‖mellinHat g z‖ ^ 2 ≤ 2 * T * Real.exp (2 * |z.re - 1 / 2| * T) *
      (∫ s : ℝ, ‖g s‖ ^ 2) := by
  let f : ℝ → ℂ := fun s => g s * Complex.exp ((z - 1 / 2) * s)
  have hc : Continuous f := hg.1.1.continuous.mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hs : HasCompactSupport f := hg.1.2.mul_right
  have hf : Integrable f := hc.integrable_of_hasCompactSupport hs
  have hf2 : Integrable (fun s => ‖f s‖ ^ 2) :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply] using hs.norm.mul_right (f' := fun s => ‖f s‖))
  have hg2 : Integrable (fun s => ‖g s‖ ^ 2) :=
    (hg.1.1.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply] using hg.1.2.norm.mul_right (f' := fun s => ‖g s‖))
  have hb : ∀ s, ‖f s‖ ^ 2 ≤
      Real.exp (2 * |z.re - 1 / 2| * T) * ‖g s‖ ^ 2 := by
    intro s
    by_cases hgs : g s = 0
    · simp [f, hgs]
    have hm := hg.2 (subset_tsupport g hgs)
    have habs : |s| ≤ T := abs_le.mpr ⟨hm.1.le, hm.2.le⟩
    have he : ((z - 1 / 2) * (s : ℂ)).re ≤ |z.re - 1 / 2| * T := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        (z.re - 1 / 2) * s ≤ |(z.re - 1 / 2) * s| := le_abs_self _
        _ = |z.re - 1 / 2| * |s| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have he2 : Real.exp (((z - 1 / 2) * (s : ℂ)).re) ^ 2 ≤
        Real.exp (2 * |z.re - 1 / 2| * T) := by
      rw [pow_two, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    dsimp [f]
    rw [norm_mul, mul_pow, Complex.norm_exp]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he2 (sq_nonneg ‖g s‖)
  have hi := (setIntegral_le_integral (s := Icc (-T) T) hf2
    (ae_of_all _ (fun s => sq_nonneg ‖f s‖))).trans
      (integral_mono hf2 (hg2.const_mul _) hb)
  rw [integral_const_mul] at hi
  have hcs := ConnesGreen.norm_integral_sq_le_mass_integral_norm_sq
    (volume.restrict (Icc (-T) T)) f hf.integrableOn hf2.integrableOn
  have he : mellinHat g z = ∫ s in Icc (-T) T, f s := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro s hn
    by_cases hgs : g s = 0
    · simp [hgs]
    have hm := hg.2 (subset_tsupport g hgs)
    exact False.elim (hn ⟨hm.1.le, hm.2.le⟩)
  rw [← he] at hcs
  have hv : (volume.restrict (Icc (-T) T)).real univ = 2 * T := by
    simp [Measure.real, Real.volume_Icc, sub_neg_eq_add, ← two_mul,
      ENNReal.toReal_ofReal, hT]
  rw [hv] at hcs
  exact hcs.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * T))
