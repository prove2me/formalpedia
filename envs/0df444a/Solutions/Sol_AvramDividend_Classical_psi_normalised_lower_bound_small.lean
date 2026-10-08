-- Prove2me | solution 1 for AvramDividend.Classical.psi_normalised_lower_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:42:11.454987+00:00
-- url     : https://prove2.me/submissions/62b4158e-5a1c-4a05-8a96-387edbc386d8

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

theorem AvramDividend.Classical.negative_jump_kernel_lower_indicator
    (θ y : ℝ) (hy : y < 0) :
    (Ioo (-1 : ℝ) 0).indicator
        (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y -
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y ≤
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y := by
  by_cases hsmall : -1 < y
  · have hs : y ∈ Ioo (-1 : ℝ) 0 := ⟨hsmall, hy⟩
    have hnotL : y ∉ Iic (-1 : ℝ) := not_le_of_gt hsmall
    have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hnotL,
      Set.indicator_of_mem hmid, sub_zero, mul_one, le_refl]
  · have hge : y ≤ -1 := le_of_not_gt hsmall
    have hbig : y ∈ Iic (-1 : ℝ) := hge
    have hnotS : y ∉ Ioo (-1 : ℝ) 0 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    have hnotM : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    simp only [Set.indicator_of_notMem hnotS, Set.indicator_of_mem hbig,
      Set.indicator_of_notMem hnotM, mul_zero, sub_zero]
    linarith [Real.exp_pos (θ * y)]

theorem AvramDividend.Classical.psi_lower_bound_by_compensated_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hlarge : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Iic (-1 : ℝ)) X.ν) :
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) ≤
      X.ψ θ := by
  let k : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 - θ * y
  let f : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y
  let g : ℝ → ℝ := fun y =>
    (Ioo (-1 : ℝ) 0).indicator k y -
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y
  have hsSubset : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := fun _ hy => hy.2
  have hlSubset : Iic (-1 : ℝ) ⊆ Iio (0 : ℝ) := by
    intro y hy
    change y ≤ (-1 : ℝ) at hy
    exact lt_of_le_of_lt hy (by norm_num)
  have hfint : IntegrableOn f (Iio (0 : ℝ)) X.ν := by
    simpa only [f] using levy_compensated_jump_integrable_nonneg X θ hθ
  have hsmall0 : IntegrableOn f (Ioo (-1 : ℝ) 0) X.ν :=
    hfint.mono_set hsSubset
  have hsmall : IntegrableOn k (Ioo (-1 : ℝ) 0) X.ν := by
    refine hsmall0.congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    simp only [f, k, Set.indicator_of_mem hmid, mul_one]
  have hsInd : IntegrableOn
      ((Ioo (-1 : ℝ) 0).indicator k) (Iio (0 : ℝ)) X.ν := by
    rw [integrableOn_indicator_iff measurableSet_Ioo,
      Set.inter_eq_left.mpr hsSubset]
    exact hsmall
  have hlInd : IntegrableOn
      ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)))
      (Iio (0 : ℝ)) X.ν := by
    rw [integrableOn_indicator_iff measurableSet_Iic,
      Set.inter_eq_left.mpr hlSubset]
    exact hlarge
  have hgint : IntegrableOn g (Iio (0 : ℝ)) X.ν :=
    hsInd.sub hlInd
  have hmono :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) ≤
        (∫ y in Iio (0 : ℝ), f y ∂X.ν) := by
    apply integral_mono_ae hgint hfint
    exact ae_restrict_of_forall_mem measurableSet_Iio (fun y hy => by
      simpa only [g, f, k] using
        negative_jump_kernel_lower_indicator θ y hy)
  have hsplit :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) =
        (∫ y in Ioo (-1 : ℝ) 0, k y ∂X.ν) -
        (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) := by
    change (∫ y in Iio (0 : ℝ),
      (Ioo (-1 : ℝ) 0).indicator k y -
        (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) = _
    rw [integral_sub hsInd hlInd,
      integral_indicator measurableSet_Ioo,
      integral_indicator measurableSet_Iic,
      Measure.restrict_restrict_of_subset hsSubset,
      Measure.restrict_restrict_of_subset hlSubset]
  have hpsidef :
      X.ψ θ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), f y ∂X.ν) := rfl
  calc
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Ioo (-1 : ℝ) 0, k y ∂X.ν) -
        (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), g y ∂X.ν) := by
          rw [hsplit]
          ring
    _ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), f y ∂X.ν) := by linarith [hmono]
    _ = X.ψ θ := hpsidef.symm

theorem AvramDividend.Classical.psi_normalised_lower_bound_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ)
    (hlarge : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Iic (-1 : ℝ)) X.ν) :
    X.c +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) / θ -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / θ ≤
      X.ψ θ / θ := by
  have hl := psi_lower_bound_by_compensated_small_jumps X θ hθ.le hlarge
  rw [hσ] at hl
  apply (le_div_iff₀ hθ).2
  have hs := div_mul_cancel₀
    (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) ∂X.ν)
    (ne_of_gt hθ)
  have hb := div_mul_cancel₀
    (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) (ne_of_gt hθ)
  nlinarith

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ)
    (hlarge : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Iic (-1 : ℝ)) X.ν) :
    X.c +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) / θ -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / θ ≤
      X.ψ θ / θ := AvramDividend.Classical.psi_normalised_lower_bound_small X hσ θ hθ hlarge
#print axioms solution
