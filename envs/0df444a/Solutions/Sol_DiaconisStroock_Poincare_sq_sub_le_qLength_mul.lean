-- Prove2me | solution 1 for DiaconisStroock.Poincare.sq_sub_le_qLength_mul
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T07:33:17.481789+00:00
-- url     : https://prove2.me/submissions/8d0f253f-281b-4f8b-95d4-608216e45baa

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare
namespace PoincarePath
lemma map_sum_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

lemma weighted {α : Type*} (l : List α) (w d : α → ℝ)
    (hw : ∀ a ∈ l, 0 < w a) :
    (l.map d).sum ^ 2 ≤ (l.map fun a => (w a)⁻¹).sum *
      (l.map fun a => w a * (d a)^2).sum := by
  simp_rw [map_sum_eq]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact le_of_lt (inv_pos.mpr (hw _ (List.get_mem _ _)))
  · intro i _; exact mul_nonneg (le_of_lt (hw _ (List.get_mem _ _))) (sq_nonneg _)
  · intro i _
    have hn : w (l.get i) ≠ 0 := ne_of_gt (hw _ (List.get_mem _ _))
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma telescope {V : Type*} (φ : V → ℝ) (p : List V) (x y : V)
    (hx : p.head? = some x) (hy : p.getLast? = some y) :
    ((pathEdges p).map fun e => φ e.2 - φ e.1).sum = φ y - φ x := by
  induction p generalizing x with
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
      have ht := ih b (by rfl) (by simpa only [List.getLast?_cons_cons] using hy)
      simpa only [pathEdges, List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.sum_cons] using (show (φ b - φ a) +
          ((pathEdges (b :: p)).map fun e => φ e.2 - φ e.1).sum = φ y - φ a by
            rw [ht]; ring)
end PoincarePath

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (x y : V) (p : List V) (hp : IsWalk P π x y p) (φ : V → ℝ) :
    (φ y - φ x)^2 ≤ qLength P π p *
      ((pathEdges p).map fun e => edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1)^2).sum := by
  have h := PoincarePath.weighted (pathEdges p)
    (fun e => edgeMeasure P π e.1 e.2) (fun e => φ e.2 - φ e.1) hp.2.2
  rw [PoincarePath.telescope φ p x y hp.1 hp.2.1] at h
  exact h
#print axioms solution

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- The per-path Cauchy–Schwarz step in the proof of Proposition 1, p. 38. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (x y : V) (p : List V) (hp : IsWalk P π x y p) (φ : V → ℝ) :
    (φ y - φ x) ^ 2 ≤ qLength P π p *
      ((pathEdges p).map fun e =>
        edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1) ^ 2).sum := by
  exact solution P hP π x y p hp φ

end DiaconisStroock.Poincare

#print axioms solution
