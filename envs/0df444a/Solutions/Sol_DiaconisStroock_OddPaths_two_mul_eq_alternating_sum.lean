-- Prove2me | solution 1 for DiaconisStroock.OddPaths.two_mul_eq_alternating_sum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:03:37.94242+00:00
-- url     : https://prove2.me/submissions/cac461cf-9c35-4b17-a31d-a32f63034957

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

set_option autoImplicit false
open DiaconisStroock.Poincare
namespace OddPathAlternating
lemma telescope {V : Type*} (φ : V → ℝ) (p : List V) (x y : V)
    (hx : p.head? = some x) (hy : p.getLast? = some y) (k : ℕ) :
    ((pathEdges p).mapIdx fun i e => (-1 : ℝ)^(k+i)*(φ e.1+φ e.2)).sum =
      (-1 : ℝ)^k * φ x - (-1 : ℝ)^(k+(pathEdges p).length)*φ y := by
  induction p generalizing x k with
  | nil => simp at hx
  | cons a p ih =>
    have ha : a = x := by simpa using hx
    subst x
    cases p with
    | nil =>
      have ha : a = y := by simpa using hy
      subst y
      simp [pathEdges]
    | cons b p =>
      have ht := ih b (by rfl) (by simpa only [List.getLast?_cons_cons] using hy) (k+1)
      have he : pathEdges (a :: b :: p) = (a,b) :: pathEdges (b :: p) := by
        simp [pathEdges]
      rw [he, List.mapIdx_cons, List.sum_cons]
      have hs : ((pathEdges (b :: p)).mapIdx fun i e =>
          (-1 : ℝ)^(k+(i+1))*(φ e.1+φ e.2)).sum =
          ((pathEdges (b :: p)).mapIdx fun i e =>
          (-1 : ℝ)^((k+1)+i)*(φ e.1+φ e.2)).sum := by
        congr 1
        congr 1
        funext i e
        rw [show k+(i+1)=(k+1)+i by omega]
      rw [hs, ht]
      simp only [Nat.add_zero, List.length_cons]
      rw [show k+1+(pathEdges (b :: p)).length = k+((pathEdges (b :: p)).length+1) by omega]
      rw [pow_succ]
      ring
end OddPathAlternating

theorem solution {V : Type*} (x : V) (p : List V) (hhead : p.head? = some x)
    (hlast : p.getLast? = some x) (hodd : Odd (pathEdges p).length) :
    ∀ φ : V → ℝ, 2*φ x =
      ((pathEdges p).mapIdx fun i e => (-1 : ℝ)^i*(φ e.1+φ e.2)).sum := by
  intro φ
  have h := OddPathAlternating.telescope φ p x x hhead hlast 0
  simp only [Nat.zero_add, pow_zero, one_mul, hodd.neg_one_pow, neg_one_mul] at h
  linarith
#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.OddPaths

example {V : Type*} (x : V) (p : List V) (hhead : p.head? = some x)
    (hlast : p.getLast? = some x) (hodd : Odd (DiaconisStroock.Poincare.pathEdges p).length) :
    ∀ φ : V → ℝ,
      2 * φ x = ((DiaconisStroock.Poincare.pathEdges p).mapIdx fun i e => (-1 : ℝ) ^ i * (φ e.1 + φ e.2)).sum := by
  exact solution x p hhead hlast hodd

end DiaconisStroock.OddPaths

#print axioms solution
