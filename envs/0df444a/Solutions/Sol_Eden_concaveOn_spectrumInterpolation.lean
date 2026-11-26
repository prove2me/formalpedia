-- Prove2me | solution 1 for Eden.concaveOn_spectrumInterpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:24.180582+00:00
-- url     : https://prove2.me/submissions/6a521676-0fe5-4d13-a19b-7470a8f77272

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
import Theorems.Thm_Eden_spectrumInterpolation_eq_min_sum
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
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
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


section
noncomputable section
open Set
namespace Eden
private theorem concaveOn_min_dimension (k : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => min d k) := by
  exact (concaveOn_id (convex_Icc 0 5)).inf
    (concaveOn_const k (convex_Icc 0 5))
private theorem concaveOn_linear_dimension (a : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => a * d) := by
  refine ⟨convex_Icc 0 5, ?_⟩
  intro x hx y hy r s hr hs hrs
  simp only [smul_eq_mul]
  exact le_of_eq (by ring)
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} (ha : Antitone a) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation a) := by
  have h01 : 0 ≤ a 0 - a 1 := sub_nonneg.mpr (ha (by decide))
  have h12 : 0 ≤ a 1 - a 2 := sub_nonneg.mpr (ha (by decide))
  have h23 : 0 ≤ a 2 - a 3 := sub_nonneg.mpr (ha (by decide))
  have h34 : 0 ≤ a 3 - a 4 := sub_nonneg.mpr (ha (by decide))
  have h := ((((concaveOn_linear_dimension (a 4)).add
    ((concaveOn_min_dimension 1).smul h01)).add
    ((concaveOn_min_dimension 2).smul h12)).add
    ((concaveOn_min_dimension 3).smul h23)).add
    ((concaveOn_min_dimension 4).smul h34)
  apply h.congr
  intro d hd
  simpa only [Pi.add_apply, smul_eq_mul] using
    (spectrumInterpolation_eq_min_sum a hd).symm
end Eden
