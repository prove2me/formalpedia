-- Prove2me | solution 1 for DiaconisStroock.Poincare.var_eq_half_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T07:33:15.548982+00:00
-- url     : https://prove2.me/submissions/fc243efc-07c0-47af-b584-4f7e04959ae7

import Mathlib
import Definitions.Def_mm_lower

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : IsDist π) (φ : V → ℝ) :
    distVar π φ = 2⁻¹ * ∑ x, ∑ y, (φ x - φ y)^2 * (π x * π y) := by
  let m := distExp π φ
  let S := ∑ x, φ x ^ 2 * π x
  have hm : (∑ x, φ x * π x) = m := rfl
  have hv : distVar π φ = S - m ^ 2 := by
    unfold distVar
    change (∑ x, (φ x - m)^2 * π x) = S - m^2
    have he : ∀ x, (φ x - m)^2 * π x =
        φ x^2 * π x - (2*m)*(φ x*π x) + m^2*π x := fun x => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hm, hπ.2]
    change S - 2*m*m + m^2*1 = S-m^2
    ring
  have hi : ∀ x, (∑ y, (φ x-φ y)^2*(π x*π y)) =
      φ x^2*π x - (2*m)*(φ x*π x) + S*π x := by
    intro x
    have he : ∀ y, (φ x-φ y)^2*(π x*π y) =
        (φ x^2*π x)*π y - (2*φ x*π x)*(φ y*π y) + (φ y^2*π y)*π x :=
      fun y => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hπ.2, hm]
    change φ x^2*π x*1 - 2*φ x*π x*m + S*π x = _
    ring
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hm, hπ.2, hv]
  change S-m^2 = 2⁻¹*(S-2*m*m+S*1)
  norm_num
  ring
#print axioms solution

namespace DiaconisStroock.Poincare

open MarkovMixing
open scoped BigOperators

/-- The first equality in the proof of Proposition 1, p. 38. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : IsDist π) (φ : V → ℝ) :
    distVar π φ = 2⁻¹ * ∑ x, ∑ y, (φ x - φ y) ^ 2 * (π x * π y) := by
  exact solution π hπ φ

end DiaconisStroock.Poincare

#print axioms solution
