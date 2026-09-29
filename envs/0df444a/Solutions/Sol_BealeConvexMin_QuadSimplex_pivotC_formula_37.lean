-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.pivotC_formula_37
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:04:28.99113+00:00
-- url     : https://prove2.me/submissions/5fbaa144-8af1-43ee-b69a-b356f4ae388e

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

open Matrix

/-- The substitution matrix: `z = S z'` with `z_p = Σ e_m z'_m`, `z_k = z'_k` for `k ≠ p`. -/
noncomputable def aux_q37_S {N : ℕ} (e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k m => if k = p then e m else if k = m then 1 else 0

lemma aux_q37_mulS {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) (p k l : Fin (N + 1)) :
    (A * aux_q37_S e p) k l = if l = p then A k p * e p else A k l + A k p * e l := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ p)]
  have h : ∀ m ∈ Finset.univ \ {p}, A k m * aux_q37_S e p m l
      = if m = l then A k m else 0 := by
    intro m hm
    have hmp : m ≠ p := by simpa using hm
    simp [aux_q37_S, hmp]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hl : l = p
  · subst hl; simp [aux_q37_S]
  · simp [aux_q37_S, hl]; ring

lemma aux_q37_Smul {N : ℕ} (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) (p k l : Fin (N + 1)) :
    ((aux_q37_S e p).transpose * B) k l = if k = p then B p l * e p else B k l + B p l * e k := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ p)]
  have h : ∀ m ∈ Finset.univ \ {p}, (aux_q37_S e p).transpose k m * B m l
      = if m = k then B m l else 0 := by
    intro m hm
    have hmp : m ≠ p := by simpa using hm
    simp [aux_q37_S, hmp]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hk : k = p
  · subst hk; simp [aux_q37_S]; ring
  · simp [aux_q37_S, hk]; ring

lemma aux_q37_pivotC_eq {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    pivotC c p d = (aux_q37_S (pivotE d p) p).transpose * (c * aux_q37_S (pivotE d p) p) := by
  have h1 : pivotCPrime c p d = c * aux_q37_S (pivotE d p) p := by
    ext k l
    rw [aux_q37_mulS]
    simp [pivotCPrime]
  ext k l
  rw [aux_q37_Smul, ← h1]
  simp [pivotC]

lemma aux_q37_quad {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (z : Fin (N + 1) → ℝ) :
    quadValue A z = z ⬝ᵥ (A *ᵥ z) := by
  simp only [quadValue, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma aux_q37_update {N : ℕ} (e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) (z' : Fin (N + 1) → ℝ) :
    Function.update z' p (∑ l, e l * z' l) = aux_q37_S e p *ᵥ z' := by
  ext k
  by_cases hk : k = p
  · subst hk; simp [aux_q37_S, Matrix.mulVec, dotProduct]
  · simp [aux_q37_S, Matrix.mulVec, dotProduct, hk]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    let e := pivotE d p
    pivotC c p d p p = c p p * e p ^ 2 ∧
    (∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l) ∧
    (∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p) ∧
    (∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l) ∧
    (c.IsSymm → (pivotC c p d).IsSymm) ∧
    ∀ z' : Fin (N + 1) → ℝ,
      quadValue c (Function.update z' p (∑ l, e l * z' l)) = quadValue (pivotC c p d) z' := by
  intro e
  have hpp : pivotC c p d p p = c p p * e p ^ 2 := by
    simp [pivotC, pivotCPrime, e]; ring
  have hpl : ∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l := by
    intro l hl
    simp [pivotC, pivotCPrime, e, hl]; ring
  have hkp : ∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p := by
    intro k hk
    simp [pivotC, pivotCPrime, e, hk]; ring
  have hkl : ∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l := by
    intro k l hk hl
    simp [pivotC, pivotCPrime, e, hk, hl]; ring
  refine ⟨hpp, hpl, hkp, hkl, ?_, ?_⟩
  · intro hc
    have hc' : ∀ i j, c j i = c i j := fun i j => hc.apply i j
    refine Matrix.IsSymm.ext fun i j => ?_
    by_cases hi : i = p <;> by_cases hj : j = p
    · subst hi; subst hj; rfl
    · subst hi; rw [hpl j hj, hkp j hj, hc' j]; ring
    · subst hj; rw [hpl i hi, hkp i hi, hc' i]; ring
    · rw [hkl i j hi hj, hkl j i hj hi, hc' i j, hc' i p, hc' j p]; ring
  · intro z'
    rw [aux_q37_update, aux_q37_pivotC_eq, aux_q37_quad, aux_q37_quad]
    set S := aux_q37_S e p
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
