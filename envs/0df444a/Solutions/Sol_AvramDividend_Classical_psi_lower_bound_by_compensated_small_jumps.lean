-- Prove2me | solution 1 for AvramDividend.Classical.psi_lower_bound_by_compensated_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:08:44.082992+00:00
-- url     : https://prove2.me/submissions/5e43401e-8a9b-425b-a1da-b183c2506e3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_negative_jump_kernel_lower_indicator

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
