-- Prove2me | solution 1 for Conway99Formal.TwoSidedSchur.distinct_column_principal_test
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:12:13.684891+00:00
-- url     : https://prove2.me/submissions/ea53248a-ff42-42d7-aecd-b5e7146e1eb5

import Definitions.Def_TwoSidedSchur
import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]









/-- The exact full-Gram contraction: `LᵀL ≤ 196I` in quadratic-form order. -/
theorem full_gram_bound (L : Matrix g e ℝ) (h : ComplementaryPSD L)
    (y : e → ℝ) : normSq (action L y) ≤ 196 * normSq y := by
  let x := action L y
  have hc := h.first x y 14
  have hp := h.second x y (-14)
  have hs : pairing L x y = normSq x := rfl
  rw [hs] at hc hp
  nlinarith

















private def pairVector [DecidableEq e] (j k : e) (t : ℝ) : e → ℝ :=
  fun z => if z = j then t else if z = k then 1 else 0

end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

open Conway99Formal.TwoSidedSchur in
theorem solution [DecidableEq e]
    (L : Matrix g e ℝ) (h : ComplementaryPSD L) (j k : e) (hjk : j ≠ k) :
    (196 - normSq (fun i => L i j)) * (196 - normSq (fun i => L i k)) ≥
      (∑ i, L i j * L i k) ^ 2 := by
  let x : g → ℝ := fun i => L i j
  let y : g → ℝ := fun i => L i k
  let b : ℝ := ∑ i, x i * y i
  have hvec (t : ℝ) : normSq (pairVector j k t) = t * t + 1 := by
    have hv (z : e) : pairVector j k t z * pairVector j k t z =
        (if z = j then t * t else 0) + (if z = k then 1 else 0) := by
      by_cases hzj : z = j
      · subst z
        simp [pairVector, hjk]
      by_cases hzk : z = k
      · subst z
        simp [pairVector, hzj]
      simp [pairVector, hzj, hzk]
    simp [normSq, hv, Finset.sum_add_distrib]
  have hact (t : ℝ) : action L (pairVector j k t) = fun i => t * x i + y i := by
    funext i
    have hv (z : e) : L i z * pairVector j k t z =
        (if z = j then L i j * t else 0) + (if z = k then L i k else 0) := by
      by_cases hzj : z = j
      · subst z
        simp [pairVector, hjk]
      by_cases hzk : z = k
      · subst z
        simp [pairVector, hzj]
      simp [pairVector, hzj, hzk]
    simp [action, hv, Finset.sum_add_distrib, x, y]
    ring
  have hexpand (t : ℝ) :
      normSq (fun i => t * x i + y i) =
        (t * t) * normSq x + (2 * t) * b + normSq y := by
    calc
      normSq (fun i => t * x i + y i) =
          ∑ i, ((t * t) * (x i * x i) + (2 * t) * (x i * y i) + y i * y i) := by
        unfold normSq
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (t * t) * normSq x + (2 * t) * b + normSq y := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
  have hpoly : ∀ t : ℝ,
      0 ≤ (196 - normSq x) * (t * t) + (-2 * b) * t + (196 - normSq y) := by
    intro t
    have hq := full_gram_bound L h (pairVector j k t)
    rw [hvec t, hact t, hexpand t] at hq
    nlinarith
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  dsimp [x, y, b] at hd ⊢
  nlinarith
