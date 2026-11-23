-- Prove2me | solution 1 for ChvatalOneHard398.SAT.satPolytope_isRationalPolyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:28:06.224489+00:00
-- url     : https://prove2.me/submissions/39c7bbd3-648f-4ca4-a532-1c0a2588057e

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

open CombOpt.ChvatalRank
open Matrix
open ChvatalOneHard398.SAT

theorem solution (F : ChvatalOneHard398.SAT.Formula) :
    IsRationalPolyhedron (ChvatalOneHard398.SAT.satPolytope F) := by
  classical
  let litA : Literal → Fin F.N → ℚ := fun l j =>
    if h : l.var < F.N then
      if j = ⟨l.var, h⟩ then (if l.pos then 1 else -1) else 0
    else 0
  let litC : Literal → ℚ := fun l =>
    if h : l.var < F.N then (if l.pos then 0 else 1) else 0
  let ix : Fin (2 * F.N + F.clauses.length) →
      (Fin 2 × Fin F.N) ⊕ Fin F.clauses.length := fun r =>
    (finSumFinEquiv.symm r).map finProdFinEquiv.symm id
  let A : Matrix (Fin (2 * F.N + F.clauses.length)) (Fin F.N) ℚ := fun r j =>
    match ix r with
    | Sum.inl (k, i) => if j = i then (if k = 0 then -1 else 1) else 0
    | Sum.inr c => -∑ l ∈ F.clauses.get c, litA l j
  let b : Fin (2 * F.N + F.clauses.length) → ℚ := fun r =>
    match ix r with
    | Sum.inl (k, _) => if k = 0 then 0 else 1
    | Sum.inr c => -1 + ∑ l ∈ F.clauses.get c, litC l
  have hone (x : Fin F.N → ℝ) (i : Fin F.N) (c : ℚ) :
      (∑ j, (((if j = i then c else 0 : ℚ) : ℝ) * x j)) = (c : ℝ) * x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp
  have hlit (x : Fin F.N → ℝ) (l : Literal) :
      literalValue x l = (litC l : ℝ) + ∑ j, (litA l j : ℝ) * x j := by
    by_cases h : l.var < F.N
    · let i : Fin F.N := ⟨l.var, h⟩
      by_cases hp : l.pos
      · simp [literalValue, litA, litC, h, hp, i, hone]
      · simp [literalValue, litA, litC, h, hp, i, hone] <;> ring
    · simp [literalValue, litA, litC, h]
  have hdecomp (x : Fin F.N → ℝ) (T : Clause) :
      (∑ l ∈ T, literalValue x l) =
        (∑ l ∈ T, (litC l : ℝ)) +
          ∑ j, (∑ l ∈ T, (litA l j : ℝ)) * x j := by
    calc
      (∑ l ∈ T, literalValue x l) =
          ∑ l ∈ T, ((litC l : ℝ) + ∑ j, (litA l j : ℝ) * x j) := by
            apply Finset.sum_congr rfl
            intro l hl
            exact hlit x l
      _ = (∑ l ∈ T, (litC l : ℝ)) +
          ∑ j, (∑ l ∈ T, (litA l j : ℝ)) * x j := by
            rw [Finset.sum_add_distrib, Finset.sum_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
  have hclause (x : Fin F.N → ℝ) (T : Clause) :
      (∑ j, (((-∑ l ∈ T, litA l j : ℚ) : ℝ) * x j)) ≤
          ((-1 + ∑ l ∈ T, litC l : ℚ) : ℝ) ↔
        1 ≤ ∑ l ∈ T, literalValue x l := by
    rw [hdecomp]
    push_cast
    simp only [map_sum, map_neg, neg_mul, Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith
  refine ⟨2 * F.N + F.clauses.length, A, b, ?_⟩
  ext x
  simp only [satPolytope, RobustToDynamics.polyhedron, Set.mem_setOf_eq]
  constructor
  · intro hx r
    cases hr : ix r with
    | inl ki =>
        rcases ki with ⟨k, i⟩
        fin_cases k
        · simpa [Matrix.map, A, b, hr, Matrix.mulVec, dotProduct, hone] using (hx.1 i).1
        · simpa [Matrix.map, A, b, hr, Matrix.mulVec, dotProduct, hone] using (hx.1 i).2
    | inr c =>
        simpa [Matrix.map, A, b, hr, Matrix.mulVec, dotProduct] using
          (hclause x (F.clauses.get c)).2 (hx.2 _ (List.get_mem _ _))
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      constructor
      · let r : Fin (2 * F.N + F.clauses.length) :=
          finSumFinEquiv (.inl (finProdFinEquiv (0, i)))
        have h := hx r
        simpa [r, Matrix.map, A, b, ix, Matrix.mulVec, dotProduct, hone] using h
      · let r : Fin (2 * F.N + F.clauses.length) :=
          finSumFinEquiv (.inl (finProdFinEquiv (1, i)))
        have h := hx r
        simpa [r, Matrix.map, A, b, ix, Matrix.mulVec, dotProduct, hone] using h
    · intro T hT
      obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hT
      let r : Fin (2 * F.N + F.clauses.length) := finSumFinEquiv (.inr c)
      have h := hx r
      exact (hclause x (F.clauses.get c)).1 (by
        simpa [r, Matrix.map, A, b, ix, Matrix.mulVec, dotProduct] using h)