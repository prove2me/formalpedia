-- Prove2me | solution 1 for DynamicsRelativity.angularMomentum_const
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T00:38:01.065752+00:00
-- url     : https://prove2.me/submissions/6177e150-6dba-4d8d-9694-9d0026d8a4cd

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_angularMomentum_deriv_zero
import Theorems.Thm_DynamicsRelativity_angularMomentum_differentiable
import Mathlib

open DynamicsRelativity

theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    angularMomentum m x t₀ = angularMomentum m x t₁ := by
  have hdiff : Differentiable ℝ (angularMomentum m x) :=
    angularMomentum_differentiable h
  have hderiv : ∀ t, deriv (angularMomentum m x) t = 0 :=
    fun t => angularMomentum_deriv_zero h t
  exact is_const_of_deriv_eq_zero hdiff hderiv t₀ t₁
