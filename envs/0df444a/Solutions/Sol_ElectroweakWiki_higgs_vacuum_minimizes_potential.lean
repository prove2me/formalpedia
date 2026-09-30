-- Prove2me | solution 1 for ElectroweakWiki.higgs_vacuum_minimizes_potential
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:49:19.41836+00:00
-- url     : https://prove2.me/submissions/0d0cf946-58a7-41ce-9c1b-4d098c6800b5

import Definitions.Def_ElectroweakWiki_defs
set_option autoImplicit false
open ElectroweakWiki Matrix

theorem solution (lam v : ℝ) (hlam : 0 < lam) :
    doubletNormSq (higgsVacuum v) = v ^ 2 / 2 ∧
      higgsPotential lam v (higgsVacuum v) = 0 ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v (higgsVacuum v) ≤ higgsPotential lam v h) ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v h = 0 ↔ doubletNormSq h = v ^ 2 / 2) := by
  have hn : doubletNormSq (higgsVacuum v) = v ^ 2 / 2 := by
    simp [doubletNormSq, higgsVacuum, Complex.normSq_ofReal, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    <;> ring
  have hp : higgsPotential lam v (higgsVacuum v) = 0 := by simp [higgsPotential, hn]
  refine ⟨hn, hp, ?_, ?_⟩
  · intro h
    rw [hp]
    unfold higgsPotential
    positivity
  · intro h
    simp [higgsPotential, mul_eq_zero, hlam.ne', sq_eq_zero_iff, sub_eq_zero]

