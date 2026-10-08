-- Prove2me | solution 1 for DiaconisStroock.OddPaths.eq_1_8
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:03:35.444632+00:00
-- url     : https://prove2.me/submissions/e4da4752-f77c-4cc6-bfb1-91e67045e483

import Mathlib
import Definitions.Def_mm_spectral

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ φ : V → ℝ, 2⁻¹ * ∑ x, ∑ y, (φ x+φ y)^2 * edgeMeasure P π x y =
      innerPi π φ φ + innerPi π φ (P.mulVec φ) := by
  intro φ
  have hc : ∀ y, ∑ x, π x * P x y = π y := by
    intro y
    exact congrFun hπ.2 y
  have ha : (∑ x, ∑ y, φ x^2 * (π x*P x y)) = innerPi π φ φ := by
    have ht : ∀ x y, φ x^2*(π x*P x y) = (φ x^2*π x)*P x y := by intros; ring
    simp_rw [ht, ← Finset.mul_sum, hP.2, mul_one]
    simp only [innerPi, pow_two]
  have hb : (∑ x, ∑ y, φ y^2 * (π x*P x y)) = innerPi π φ φ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hc]
    simp only [innerPi, pow_two]
  have hd : (∑ x, ∑ y, φ x*φ y*(π x*P x y)) = innerPi π φ (P.mulVec φ) := by
    change (∑ x, ∑ y, φ x*φ y*(π x*P x y)) =
      ∑ x, φ x * (∑ y, P x y * φ y) * π x
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have ht : ∀ x y, (φ x+φ y)^2 * edgeMeasure P π x y =
      φ x^2*(π x*P x y) + φ y^2*(π x*P x y) + 2*(φ x*φ y*(π x*P x y)) := by
    intro x y
    unfold edgeMeasure
    ring
  have hd2 : (∑ x, ∑ y, 2*(φ x*φ y*(π x*P x y))) =
      2 * (∑ x, ∑ y, φ x*φ y*(π x*P x y)) := by
    simp only [Finset.mul_sum]
  simp_rw [ht, Finset.sum_add_distrib]
  rw [ha, hb, hd2, hd]
  ring
#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.OddPaths

example {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ φ : V → ℝ, 2⁻¹ * ∑ x, ∑ y, (φ x + φ y) ^ 2 * edgeMeasure P π x y =
      innerPi π φ φ + innerPi π φ (P.mulVec φ) := by
  exact solution P hP π hπ

end DiaconisStroock.OddPaths

#print axioms solution
