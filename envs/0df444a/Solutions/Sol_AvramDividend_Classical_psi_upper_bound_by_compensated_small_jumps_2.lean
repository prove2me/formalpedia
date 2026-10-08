-- Prove2me | solution 2 for AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:42:46.143639+00:00
-- url     : https://prove2.me/submissions/4fcf8323-e2c3-4b5c-94c9-60b4419758d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_negative_jump_kernel_upper_indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) := by
  let k : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 - θ * y
  let f : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y
  let g : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator k
  have hs : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) :=
    fun _ hy => hy.2
  have hfint : IntegrableOn f (Iio (0 : ℝ)) X.ν := by
    simpa only [f] using
      levy_compensated_jump_integrable_nonneg X θ hθ
  have hsmall0 : IntegrableOn f (Ioo (-1 : ℝ) 0) X.ν :=
    hfint.mono_set hs
  have hsmall : IntegrableOn k (Ioo (-1 : ℝ) 0) X.ν := by
    refine hsmall0.congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hmid : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hy.1, by linarith [hy.2]⟩
    simp only [f, k, Set.indicator_of_mem hmid, mul_one]
  have hgint : IntegrableOn g (Iio (0 : ℝ)) X.ν := by
    change IntegrableOn
      ((Ioo (-1 : ℝ) 0).indicator k) (Iio (0 : ℝ)) X.ν
    rw [integrableOn_indicator_iff measurableSet_Ioo,
      Set.inter_eq_left.mpr hs]
    exact hsmall
  have hmono :
      (∫ y in Iio (0 : ℝ), f y ∂X.ν) ≤
        (∫ y in Iio (0 : ℝ), g y ∂X.ν) := by
    apply integral_mono_ae hfint hgint
    exact ae_restrict_of_forall_mem measurableSet_Iio
      (fun y hy => by
        simpa only [g, f, k] using
          negative_jump_kernel_upper_indicator θ y hθ hy)
  have hsplit :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) =
        (∫ y in Ioo (-1 : ℝ) 0, k y ∂X.ν) := by
    change (∫ y in Iio (0 : ℝ),
      (Ioo (-1 : ℝ) 0).indicator k y ∂X.ν) = _
    rw [integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict_of_subset hs]
  have hψ :
      X.ψ θ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), f y ∂X.ν) := rfl
  calc
    X.ψ θ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), f y ∂X.ν) := hψ
    _ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), g y ∂X.ν) := by linarith [hmono]
    _ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Ioo (-1 : ℝ) 0, k y ∂X.ν) := by
      rw [hsplit]
