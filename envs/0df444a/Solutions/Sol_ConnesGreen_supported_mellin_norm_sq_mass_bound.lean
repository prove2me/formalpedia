-- Prove2me | solution 1 for ConnesGreen.supported_mellin_norm_sq_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T20:42:16.002497+00:00
-- url     : https://prove2.me/submissions/9bb2e772-dca1-4da5-8cab-3d264fb93101

import Definitions.Def_ConnesRZ_weil_defs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ Set
noncomputable section

private theorem finite_measure_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let m := μ.real univ
  let J := ∫ x, ‖f x‖ ∂μ
  let L := ∫ x, ‖f x‖ ^ 2 ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  have hJ : 0 ≤ J := integral_nonneg (fun x => norm_nonneg _)
  have hnorm : ‖∫ x, f x ∂μ‖ ≤ J := norm_integral_le_integral_norm f
  have hv : 0 ≤ ∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ) = m ^ 2 * L - m * J ^ 2 := by
    simp_rw [show ∀ x, (m * ‖f x‖ - J) ^ 2 =
      m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖ + J ^ 2 by intro x; ring]
    have hd : Integrable (fun x => m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖) μ :=
      (hf2.const_mul _).sub (hf.norm.const_mul _)
    rw [integral_add hd (integrable_const _),
      integral_sub (hf2.const_mul _) (hf.norm.const_mul _), integral_const_mul,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul]
    dsimp [m, J, L]
    ring
  rw [he] at hv
  by_cases hm0 : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact ((ENNReal.toReal_eq_zero_iff (μ univ)).mp hm0).resolve_right
        (measure_ne_top μ univ)
    simp [hμ]
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hsq : J ^ 2 ≤ m * L := by nlinarith
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq

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
  have hcs := finite_measure_bound
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
