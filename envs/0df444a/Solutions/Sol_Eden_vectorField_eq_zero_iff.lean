-- Prove2me | solution 1 for Eden.vectorField_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:58.221871+00:00
-- url     : https://prove2.me/submissions/af8e5ea3-554d-4e4a-bf0e-3e92637b12ea

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_eq_zero_of_radii_and_fifth_zero
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


attribute [local simp] Eden.evolution_origin

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) (p : PhaseSpace) :
    vectorField c p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h₀ : q (radiusSq₁ p) * p 0 - p 1 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 0) h
    have h₁ : q (radiusSq₁ p) * p 1 + p 0 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 1) h
    have h₂ : q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 2) h
    have h₃ : q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 3) h
    have hw : -c * p 4 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 4) h
    apply eq_zero_of_radii_and_fifth_zero
    · dsimp [radiusSq₁]
      nlinarith [congrArg (fun a : ℝ => p 0 * a) h₁,
        congrArg (fun a : ℝ => p 1 * a) h₀]
    · have hprod : Real.sqrt 2 * (p 2 ^ 2 + p 3 ^ 2) = 0 := by
        nlinarith [congrArg (fun a : ℝ => p 2 * a) h₃,
          congrArg (fun a : ℝ => p 3 * a) h₂]
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (by positivity))
    · exact (mul_eq_zero.mp hw).resolve_left (neg_ne_zero.mpr hc)
  · rintro rfl
    ext i
    fin_cases i <;> simp [vectorField, radiusSq₁, radiusSq₂]
end Eden
