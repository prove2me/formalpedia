-- Prove2me | solution 1 for Eden.spectrumInterpolation_eq_min_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:10.03815+00:00
-- url     : https://prove2.me/submissions/367e918c-a6a7-4269-a05a-b356ac3c7e54

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
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
private theorem singularWeight_eq_min_sub (d : ℝ) (i : ℕ) :
    singularWeight i d = min d (i + 1) - min d i := by
  unfold singularWeight
  by_cases hdi : d ≤ i
  · rw [max_eq_left (by linarith), min_eq_left hdi,
      min_eq_left (show d ≤ (i : ℝ) + 1 by linarith)]
    norm_num
  · have hid : (i : ℝ) ≤ d := le_of_lt (lt_of_not_ge hdi)
    rw [max_eq_right (by linarith), min_eq_right hid]
    by_cases hdi' : d ≤ (i : ℝ) + 1
    · rw [min_eq_left hdi', min_eq_right (show d - (i : ℝ) ≤ 1 by linarith)]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hdi')),
        min_eq_left (show 1 ≤ d - (i : ℝ) by linarith)]
      ring
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) {d : ℝ}
    (hd : d ∈ Icc 0 5) :
    spectrumInterpolation a d = a 4 * d +
      (a 0 - a 1) * min d 1 + (a 1 - a 2) * min d 2 +
      (a 2 - a 3) * min d 3 + (a 3 - a 4) * min d 4 := by
  unfold spectrumInterpolation
  simp only [singularWeight_eq_min_sub]
  norm_num [Fin.sum_univ_succ, min_eq_right hd.1, min_eq_left hd.2]
  simp only [show Fin.succ (2 : Fin 4) = (3 : Fin 5) from rfl,
    show (Fin.succ (2 : Fin 3)).succ = (4 : Fin 5) from rfl]
  ring
end Eden
