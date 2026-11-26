-- Prove2me | solution 1 for Eden.contDiff_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:30.533608+00:00
-- url     : https://prove2.me/submissions/baaf5274-5129-49ed-be9b-a3d736799b57

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_contDiffAt_planarAmplitude
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
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (evolution c t) := by
  have h₁ : ContDiff ℝ n (fun p : PhaseSpace =>
      planarAmplitude t (p 0 ^ 2 + p 1 ^ 2)) := by
    apply contDiff_iff_contDiffAt.2
    intro p
    have hr : ContDiffAt ℝ n (fun p : PhaseSpace => p 0 ^ 2 + p 1 ^ 2) p := by
      fun_prop
    have h := (contDiffAt_planarAmplitude ht
      (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))) n).comp p hr
    exact h
  have h₂ : ContDiff ℝ n (fun p : PhaseSpace =>
      planarAmplitude t (p 2 ^ 2 + p 3 ^ 2)) := by
    apply contDiff_iff_contDiffAt.2
    intro p
    have hr : ContDiffAt ℝ n (fun p : PhaseSpace => p 2 ^ 2 + p 3 ^ 2) p := by
      fun_prop
    have h := (contDiffAt_planarAmplitude ht
      (add_nonneg (sq_nonneg (p 2)) (sq_nonneg (p 3))) n).comp p hr
    exact h
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [evolution, planarX, planarY] <;> fun_prop
end Eden
