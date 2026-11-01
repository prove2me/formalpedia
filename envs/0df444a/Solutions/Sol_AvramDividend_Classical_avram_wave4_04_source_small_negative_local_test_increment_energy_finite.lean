-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_source_small_negative_local_test_increment_energy_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:25:58.611047+00:00
-- url     : https://prove2.me/submissions/60929434-78ce-4ff1-91e8-f2d3e1fc0692

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Original-Lévy small-mark test-function quadratic energy, with a local C1
interior band and the source ν square Lévy bound. This is a finite-energy
prerequisite for a compensated Itô–Meyer test-function jump martingale.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (x δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hxu : u + δ ≤ x) (hxv : x ≤ v) :
    (∫⁻ z in Ioo (-δ) (0 : ℝ),
      ENNReal.ofReal ((w (x + z) - w x) ^ 2) ∂X.ν) < ⊤ := by
  obtain ⟨M, hMnonneg, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval w a b u v hw hau huv hvb
  have hdiff (t : ℝ) (ht : t ∈ Icc u v) : DifferentiableAt ℝ w t := by
    have hopen : t ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hau ht.1, lt_of_le_of_lt ht.2 hvb⟩
    exact (hw.contDiffAt (isOpen_Ioo.mem_nhds hopen)).differentiableAt (by norm_num)
  have hderivnorm (t : ℝ) (ht : t ∈ Icc u v) : ‖deriv w t‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hderiv t ht.1 ht.2
  have hLip (z : ℝ) (hz : z ∈ Ioo (-δ) (0 : ℝ)) :
      ‖w (x + z) - w x‖ ≤ M * ‖z‖ := by
    have hxmem : x ∈ Icc u v := ⟨by linarith, hxv⟩
    have hxzmem : x + z ∈ Icc u v :=
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hraw := (convex_Icc u v).norm_image_sub_le_of_norm_deriv_le
      hdiff hderivnorm hxmem hxzmem
    simpa only [add_sub_cancel_left] using hraw
  have hpoint (z : ℝ) (hz : z ∈ Ioo (-δ) (0 : ℝ)) :
      ENNReal.ofReal ((w (x + z) - w x) ^ 2) ≤
        ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (min 1 (z ^ 2)) := by
    have hsmall : z ^ 2 ≤ 1 := by
      have hzlo := hz.1
      have hzhi := hz.2
      nlinarith [sq_nonneg (z + 1)]
    have hmin : min 1 (z ^ 2) = z ^ 2 := min_eq_right hsmall
    have hsq : (w (x + z) - w x) ^ 2 ≤ M ^ 2 * z ^ 2 := by
      have hb := hLip z hz
      have hb2 := pow_le_pow_left₀ (norm_nonneg (w (x + z) - w x)) hb 2
      calc
        (w (x + z) - w x) ^ 2 = ‖w (x + z) - w x‖ ^ 2 := by
          simp [Real.norm_eq_abs, sq_abs]
        _ ≤ (M * ‖z‖) ^ 2 := hb2
        _ = M ^ 2 * z ^ 2 := by
          simp [mul_pow, Real.norm_eq_abs, sq_abs]
    rw [← ENNReal.ofReal_mul (sq_nonneg M), hmin]
    exact ENNReal.ofReal_le_ofReal hsq
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  calc
    (∫⁻ z in Ioo (-δ) (0 : ℝ),
        ENNReal.ofReal ((w (x + z) - w x) ^ 2) ∂X.ν)
        ≤ ∫⁻ z in Ioo (-δ) (0 : ℝ),
          ENNReal.ofReal (M ^ 2) *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
            apply setLIntegral_mono (by fun_prop)
            intro z hz
            exact hpoint z hz
    _ ≤ ∫⁻ z : ℝ,
          ENNReal.ofReal (M ^ 2) *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν :=
          setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (M ^ 2) *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
          exact lintegral_const_mul _ hνmeas
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.ν_integrable
