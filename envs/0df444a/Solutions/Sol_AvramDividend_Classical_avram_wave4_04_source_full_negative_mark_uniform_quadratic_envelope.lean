-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:35:45.971992+00:00
-- url     : https://prove2.me/submissions/be76a8ca-ea05-4a68-979f-89b67d72da85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Uniform original-source negative-mark quadratic jump envelope throughout
a compact stopped interior reserve band, including ruin overshoot marks.
The global measure bound uses only the source Levy square-energy condition.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ y : ℝ, y ∈ Icc (u + δ) v →
        ∀ z : ℝ, z < 0 →
          (w (y + z) - w y) ^ 2 ≤ K * min 1 (z ^ 2)) ∧
      (∀ y : ℝ, y ∈ Icc (u + δ) v →
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (y + z) - w y) ^ 2) ∂X.ν) < ⊤) := by
  obtain ⟨M, hMnonneg, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval w a b u v hw hau huv hvb
  have hv0 : 0 ≤ v := by linarith
  have hcont : ContinuousOn w (Icc (0 : ℝ) v) :=
    hw_cont.mono (by intro t ht; exact ht.1)
  obtain ⟨N, hN⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) v)).exists_bound_of_continuousOn hcont
  have hNnonneg : 0 ≤ N :=
    le_trans (norm_nonneg (w v)) (hN v ⟨hv0, le_refl v⟩)
  have hdiff (t : ℝ) (ht : t ∈ Icc u v) : DifferentiableAt ℝ w t := by
    have hopen : t ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hau ht.1, lt_of_le_of_lt ht.2 hvb⟩
    exact (hw.contDiffAt (isOpen_Ioo.mem_nhds hopen)).differentiableAt (by norm_num)
  have hderivnorm (t : ℝ) (ht : t ∈ Icc u v) : ‖deriv w t‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hderiv t ht.1 ht.2
  let K : ℝ := M ^ 2 + ((2 * N) / δ) ^ 2
  have hKnonneg : 0 ≤ K := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint (y : ℝ) (hy : y ∈ Icc (u + δ) v)
      (z : ℝ) (hz : z < 0) :
      (w (y + z) - w y) ^ 2 ≤ K * min 1 (z ^ 2) := by
    by_cases hnear : -δ < z
    · have hymem : y ∈ Icc u v := ⟨by linarith [hy.1], hy.2⟩
      have hyzmem : y + z ∈ Icc u v :=
        ⟨by linarith [hy.1, hnear], by linarith [hy.2, hz]⟩
      have hLip : ‖w (y + z) - w y‖ ≤ M * ‖z‖ := by
        have hraw := (convex_Icc u v).norm_image_sub_le_of_norm_deriv_le
          hdiff hderivnorm hymem hyzmem
        simpa only [add_sub_cancel_left] using hraw
      have hzsq : z ^ 2 ≤ 1 := by
        have hzlo : -1 < z := by linarith
        nlinarith [sq_nonneg (z + 1)]
      have hmin : min 1 (z ^ 2) = z ^ 2 := min_eq_right hzsq
      have hsq : (w (y + z) - w y) ^ 2 ≤ M ^ 2 * z ^ 2 := by
        have hb2 := pow_le_pow_left₀ (norm_nonneg (w (y + z) - w y)) hLip 2
        calc
          (w (y + z) - w y) ^ 2 = ‖w (y + z) - w y‖ ^ 2 := by
            simp [Real.norm_eq_abs, sq_abs]
          _ ≤ (M * ‖z‖) ^ 2 := hb2
          _ = M ^ 2 * z ^ 2 := by
            simp [mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hmin]
      exact hsq.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg z))
    · have hzfar : z ≤ -δ := le_of_not_gt hnear
      have hylow : 0 ≤ y := by linarith [hy.1]
      have hNy : ‖w y‖ ≤ N := hN y ⟨hylow, hy.2⟩
      have hNyz : ‖w (y + z)‖ ≤ N := by
        by_cases hneg : y + z < 0
        · rw [hw_neg (y + z) hneg]
          simpa using hNnonneg
        · apply hN (y + z)
          exact ⟨le_of_not_gt hneg, by linarith [hy.2, hz]⟩
      have hnorm : ‖w (y + z) - w y‖ ≤ 2 * N := by
        calc
          ‖w (y + z) - w y‖ ≤ ‖w (y + z)‖ + ‖w y‖ :=
            norm_sub_le _ _
          _ ≤ 2 * N := by linarith
      have hsq : (w (y + z) - w y) ^ 2 ≤ (2 * N) ^ 2 := by
        have hb2 := pow_le_pow_left₀ (norm_nonneg (w (y + z) - w y)) hnorm 2
        calc
          (w (y + z) - w y) ^ 2 = ‖w (y + z) - w y‖ ^ 2 := by
            simp [Real.norm_eq_abs, sq_abs]
          _ ≤ (2 * N) ^ 2 := hb2
      have hδsq : δ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - δ)]
      have hzsq : δ ^ 2 ≤ z ^ 2 := by nlinarith [sq_nonneg (z + δ)]
      have hminlower : δ ^ 2 ≤ min 1 (z ^ 2) := le_min hδsq hzsq
      have hiden : ((2 * N) / δ) ^ 2 * δ ^ 2 = (2 * N) ^ 2 := by
        field_simp [ne_of_gt hδ]
      calc
        (w (y + z) - w y) ^ 2 ≤ (2 * N) ^ 2 := hsq
        _ = ((2 * N) / δ) ^ 2 * δ ^ 2 := hiden.symm
        _ ≤ ((2 * N) / δ) ^ 2 * min 1 (z ^ 2) :=
          mul_le_mul_of_nonneg_left hminlower (sq_nonneg _)
        _ ≤ K * min 1 (z ^ 2) :=
          mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left (sq_nonneg _))
            (le_min (by norm_num) (sq_nonneg z))
  refine ⟨K, hKnonneg, hpoint, ?_⟩
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  intro y hy
  have hbound (z : ℝ) (hz : z ∈ Iio (0 : ℝ)) :
      ENNReal.ofReal ((w (y + z) - w y) ^ 2) ≤
        ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) := by
    rw [← ENNReal.ofReal_mul hKnonneg]
    exact ENNReal.ofReal_le_ofReal (hpoint y hy z hz)
  calc
    (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((w (y + z) - w y) ^ 2) ∂X.ν)
      ≤ ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
            apply setLIntegral_mono (by fun_prop)
            intro z hz
            exact hbound z hz
    _ ≤ ∫⁻ z : ℝ,
          ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν :=
      setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) :=
      lintegral_const_mul _ hνmeas
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.ν_integrable