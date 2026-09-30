-- Prove2me | solution 1 for ElectroweakWiki.electric_charge_unbroken
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:49:20.097987+00:00
-- url     : https://prove2.me/submissions/7432eed9-6870-43b0-8f21-d2e713f839c7

import Definitions.Def_ElectroweakWiki_defs
set_option autoImplicit false
open ElectroweakWiki Matrix

theorem higgs_minimum (lam v : ℝ) (hlam : 0 < lam) :
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

theorem solution (v : ℝ) (hv : v ≠ 0) :
    isospinHyperchargeGenerator 1 1 *ᵥ higgsVacuum v = 0 ∧
      electricCharge (-1 / 2) 1 = 0 ∧
      (∀ a b : ℝ, isospinHyperchargeGenerator a b *ᵥ higgsVacuum v = 0 ↔ a = b) := by
  have hg (a b : ℝ) : isospinHyperchargeGenerator a b *ᵥ higgsVacuum v =
      ![0, (((b-a)*v/(2*Real.sqrt 2) : ℝ) : ℂ)] := by
    ext i
    fin_cases i <;>
      simp [isospinHyperchargeGenerator, higgsVacuum, pauli, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] <;> push_cast <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    simp
  · norm_num [electricCharge]
  · intro a b
    constructor
    · intro h
      rw [hg] at h
      have h1 := congrArg (fun f : Fin 2 → ℂ => f 1) h
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
      have hz : (b-a)*v/(2*Real.sqrt 2) = 0 := by exact_mod_cast h1
      have hden : 2 * Real.sqrt 2 ≠ 0 := by positivity
      have hz' : (b-a)*v = 0 := (div_eq_zero_iff.mp hz).resolve_right hden
      have hab := (mul_eq_zero.mp hz').resolve_right hv
      linarith
    · intro h
      rw [hg, h]
      simp

