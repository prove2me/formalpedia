-- Prove2me | solution 1 for Eden.first_plane_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:05.152466+00:00
-- url     : https://prove2.me/submissions/3995f599-5a49-4893-92e6-69d2060c4783

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_at_one
import Theorems.Thm_Eden_planarAmplitude_at_two
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278
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


attribute [local simp] Eden.evolution_origin

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0) :
    evolution c (2 * Real.pi) p = p := by
  have ht : 0 ≤ 2 * Real.pi := by positivity
  have hg : planarAmplitude (2 * Real.pi) (p 0 ^ 2 + p 1 ^ 2) = 1 := by
    change planarAmplitude (2 * Real.pi) (radiusSq₁ p) = 1
    rcases h₁ with h₁ | h₁
    · rw [h₁, planarAmplitude_at_one ht]
    · rw [h₁, planarAmplitude_at_two ht]
  obtain ⟨h₂, h₃⟩ := (radiusSq₂_eq_zero_iff p).mp h₂
  ext i
  fin_cases i <;> simp [evolution, planarX, planarY, hg, h₂, h₃, hw]
end Eden
