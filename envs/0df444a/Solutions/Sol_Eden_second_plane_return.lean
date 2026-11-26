-- Prove2me | solution 1 for Eden.second_plane_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:06.968658+00:00
-- url     : https://prove2.me/submissions/1573df3e-7ca9-4f14-aa82-a4751b7a803f

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
import Theorems.Thm_P2M_Eden_radiusSq__eq_zero_iff_1d70f4110486
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
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 1 ∨ radiusSq₂ p = 2)
    (hw : p 4 = 0) : evolution c (2 * Real.pi / Real.sqrt 2) p = p := by
  have ht : 0 ≤ 2 * Real.pi / Real.sqrt 2 := by positivity
  have hangle : Real.sqrt 2 * (2 * Real.pi / Real.sqrt 2) = 2 * Real.pi := by
    field_simp
  have hg : planarAmplitude (2 * Real.pi / Real.sqrt 2) (p 2 ^ 2 + p 3 ^ 2) = 1 := by
    change planarAmplitude (2 * Real.pi / Real.sqrt 2) (radiusSq₂ p) = 1
    rcases h₂ with h₂ | h₂
    · rw [h₂, planarAmplitude_at_one ht]
    · rw [h₂, planarAmplitude_at_two ht]
  obtain ⟨h₀, h₁⟩ := (radiusSq₁_eq_zero_iff p).mp h₁
  ext i
  fin_cases i <;> simp [evolution, planarX, planarY, hg, hangle, h₀, h₁, hw]
end Eden
