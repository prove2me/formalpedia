-- Prove2me | solution 1 for Eden.contDiffAt_evolution_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:05.303815+00:00
-- url     : https://prove2.me/submissions/b923e07c-97f8-4a2e-bc0d-b27566119934

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
import Theorems.Thm_Eden_contDiffAt_planarAmplitude_joint
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
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
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2) (t, p) := by
  have hamp (i j : Fin 5) : ContDiffAt ℝ n
      (fun u : ℝ × PhaseSpace => planarAmplitude u.1 (u.2 i ^ 2 + u.2 j ^ 2)) (t, p) := by
    have hr : ContDiffAt ℝ n
        (fun u : ℝ × PhaseSpace => (u.1, u.2 i ^ 2 + u.2 j ^ 2)) (t, p) := by
      fun_prop
    have h := (contDiffAt_planarAmplitude_joint ht
      (add_nonneg (sq_nonneg (p i)) (sq_nonneg (p j))) n).comp (t, p) hr
    exact h
  rw [contDiffAt_piLp]
  intro i
  fin_cases i <;> simp [evolution, planarX, planarY] <;> fun_prop
end Eden
