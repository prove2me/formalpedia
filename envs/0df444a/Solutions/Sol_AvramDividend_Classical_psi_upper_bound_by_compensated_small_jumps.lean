-- Prove2me | solution 1 for AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:33:11.555984+00:00
-- url     : https://prove2.me/submissions/495b48c4-0ca7-4587-98a5-d469dba44eae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.exp_neg_remainder_bounds (z : ℝ) (hz : z ≤ 0) :
    0 ≤ Real.exp z - 1 - z ∧ Real.exp z - 1 - z ≤ z ^ 2 := by
  constructor
  · linarith [Real.add_one_le_exp z]
  · by_cases hnear : -1 ≤ z
    · have hzabs : |z| ≤ 1 := abs_le.mpr ⟨hnear, by linarith⟩
      exact (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hzabs)
    · have hfar : z ≤ -1 := le_of_not_ge hnear
      have hexp : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hz
      have hprod : 0 ≤ (-z) * (-z - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]

theorem AvramDividend.Classical.levy_compensated_jump_integrable_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * y * ((Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) X.ν := by
  let f : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 -
      θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
  have hmin_meas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y =>
      le_min (by norm_num) (sq_nonneg y))
  have hmin_int :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmin_meas.aestronglyMeasurable hmin_nonneg).mp
        (ne_of_lt X.ν_integrable)
  have hdom_int :
      Integrable (fun y : ℝ => (1 + θ ^ 2) * min 1 (y ^ 2)) X.ν :=
    hmin_int.const_mul _
  have hind_meas :
      Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hf_meas : Measurable f := by
    dsimp [f]
    fun_prop
  have hbound (y : ℝ) (hy : y < 0) :
      |f y| ≤ (1 + θ ^ 2) * min 1 (y ^ 2) := by
    have hz : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
    by_cases hsmall : -1 < y
    · have hmem : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hsmall, by linarith⟩
      have hy2 : y ^ 2 ≤ 1 := by
        have hp : 0 ≤ (1 + y) * (1 - y) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hr := exp_neg_remainder_bounds (θ * y) hz
      have hb :
          |Real.exp (θ * y) - 1 - θ * y| ≤
            (1 + θ ^ 2) * y ^ 2 := by
        rw [abs_of_nonneg hr.1]
        nlinarith [hr.2, sq_nonneg y]
      simpa only [f, Set.indicator_of_mem hmem, mul_one,
        min_eq_right hy2] using hb
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 :=
        fun h => hsmall h.1
      have hle : y ≤ -1 := le_of_not_gt hsmall
      have hy2 : 1 ≤ y ^ 2 := by
        have hp : 0 ≤ (-y - 1) * (-y + 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have he0 : 0 ≤ Real.exp (θ * y) :=
        (Real.exp_pos _).le
      have he1 : Real.exp (θ * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr hz
      have hb :
          |Real.exp (θ * y) - 1| ≤
            (1 + θ ^ 2) * 1 := by
        rw [abs_of_nonpos (by linarith)]
        nlinarith [sq_nonneg θ]
      have hindicator :
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y = 0 := by
        simp [Set.indicator, hnot]
      simpa only [f, hindicator, mul_zero,
        sub_zero, min_eq_left hy2] using hb
  apply Integrable.mono' hdom_int.restrict hf_meas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with y hy
  simpa only [Real.norm_eq_abs] using hbound y hy


private theorem kernel_upper (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ≤
    (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y := by
  by_cases hs : -1 < y
  · have hm : y ∈ Ioo (-1 : ℝ) 1 := ⟨hs, by linarith⟩
    have hm' : y ∈ Ioo (-1 : ℝ) 0 := ⟨hs, hy⟩
    simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hm', mul_one, le_refl]
  · have hm : y ∉ Ioo (-1 : ℝ) 1 := fun h => hs h.1
    have hm' : y ∉ Ioo (-1 : ℝ) 0 := fun h => hs h.1
    simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm', mul_zero, sub_zero]
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hθ hy.le))

theorem AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) := by
  let k : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 - θ * y
  let f : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 -
    θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
  have hs : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := fun _ hy => hy.2
  have hf : IntegrableOn f (Iio (0 : ℝ)) X.ν :=
    levy_compensated_jump_integrable_nonneg X θ hθ
  have hk : IntegrableOn k (Ioo (-1 : ℝ) 0) X.ν := by
    refine (hf.mono_set hs).congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hm : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    simp only [f, k, Set.indicator_of_mem hm, mul_one]
  have hi : IntegrableOn ((Ioo (-1 : ℝ) 0).indicator k) (Iio (0 : ℝ)) X.ν := by
    rw [integrableOn_indicator_iff measurableSet_Ioo, Set.inter_eq_left.mpr hs]
    exact hk
  have hm : (∫ y in Iio (0 : ℝ), f y ∂X.ν) ≤
      ∫ y in Iio (0 : ℝ), (Ioo (-1 : ℝ) 0).indicator k y ∂X.ν := by
    apply integral_mono_ae hf hi
    exact ae_restrict_of_forall_mem measurableSet_Iio
      (fun y hy => kernel_upper θ y hθ hy)
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict_of_subset hs] at hm
  change X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 + (∫ y in Iio (0 : ℝ), f y ∂X.ν) ≤ _
  exact add_le_add_right hm _

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) := AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps X θ hθ

#print axioms solution

