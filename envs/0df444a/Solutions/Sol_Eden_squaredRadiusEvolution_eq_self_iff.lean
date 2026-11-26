-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:37.039419+00:00
-- url     : https://prove2.me/submissions/27088fda-6b82-4416-aa5a-aed7d4695936

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_RadialReturns
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
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos
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
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 < t) :
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 := by
  constructor
  · intro h
    by_cases hs : s = 1
    · exact Or.inr (Or.inl hs)
    have hR := sqrt_radialDiscriminant_pos ht.le s
    have hratio : (s - 1) / Real.sqrt (radialDiscriminant t s) = s - 1 := by
      dsimp [squaredRadiusEvolution] at h
      linarith
    have hmul := (div_eq_iff (ne_of_gt hR)).mp hratio
    have hprod : (s - 1) * (Real.sqrt (radialDiscriminant t s) - 1) = 0 := by
      nlinarith
    have hroot : Real.sqrt (radialDiscriminant t s) = 1 := by
      have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hs)
      linarith
    have hD : radialDiscriminant t s = 1 := by
      have hsq := Real.sq_sqrt (radialDiscriminant_pos ht.le s).le
      rw [hroot] at hsq
      nlinarith
    have hE : 0 < 1 - Real.exp (-4 * t) := by
      have := Real.exp_lt_one_iff.mpr (show -4 * t < 0 by linarith)
      linarith
    have hprod₂ : (1 - Real.exp (-4 * t)) * (s * (s - 2)) = 0 := by
      dsimp [radialDiscriminant] at hD
      nlinarith
    have hsprod := (mul_eq_zero.mp hprod₂).resolve_left (ne_of_gt hE)
    rcases mul_eq_zero.mp hsprod with hs₀ | hs₂
    · exact Or.inl hs₀
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> simp
end Eden
