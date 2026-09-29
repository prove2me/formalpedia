-- Prove2me | solution 1 for DynamicsRelativity.angularMomentum_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T00:47:48.204881+00:00
-- url     : https://prove2.me/submissions/4ca2a492-8aca-441b-95e7-d2cb6d6d16ca

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Theorems.Thm_DynamicsRelativity_angularMomentum_deriv_eq_cross_acc
import Theorems.Thm_DynamicsRelativity_cross_position_acc_zero
import Mathlib

open DynamicsRelativity

theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t : ℝ) :
    deriv (angularMomentum m x) t = 0 := by
  rw [angularMomentum_deriv_eq_cross_acc h t]
  rw [cross_position_acc_zero h t]
  exact smul_zero m
