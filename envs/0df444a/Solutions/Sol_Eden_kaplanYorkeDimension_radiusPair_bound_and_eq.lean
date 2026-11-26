-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_radiusPair_bound_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:14.900124+00:00
-- url     : https://prove2.me/submissions/92b7ce0a-6e13-44e4-9d07-a8a1ffdce011

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_zero
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
import Theorems.Thm_Eden_kaplanYorkeDimension_one_one
import Theorems.Thm_Eden_kaplanYorkeDimension_one_two
import Theorems.Thm_Eden_kaplanYorkeDimension_two_two
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_targetDimension_bounds
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2) :
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) := by
  rcases hs₁ with rfl | rfl | rfl <;> rcases hs₂ with rfl | rfl | rfl
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals simp only [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc, kaplanYorkeDimension_zero_zero hc,
    kaplanYorkeDimension_zero_one hc, kaplanYorkeDimension_zero_two hc,
    kaplanYorkeDimension_one_one hc, kaplanYorkeDimension_one_two hc,
    kaplanYorkeDimension_two_two hc]
  all_goals norm_num
  all_goals constructor <;> linarith [(targetDimension_bounds hc).1]
end Eden
