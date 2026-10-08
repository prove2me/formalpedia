-- Prove2me | solution 1 for FriezeKannan.CutDecomp.frobenius_drop
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:08:21.395534+00:00
-- url     : https://prove2.me/submissions/29221087-22c2-457d-ad40-f3931fa4748d

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

open FriezeKannan.CutDecomp

/-- §4.1, proof of Theorem 7, p. 188: subtracting `CUT(S, T, d)` with
`d = W(S, T)/(|S||T|)` lowers `‖W‖²_F` by exactly `|S||T| d² = W(S, T)²/(|S||T|)`. -/
theorem solution {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (W : Matrix R C ℝ) (S : Finset R) (T : Finset C) (hS : S.Nonempty) (hT : T.Nonempty) :
    let d : ℝ := blockSum W S T / ((S.card : ℝ) * T.card)
    (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = ∑ i ∈ S, ∑ j ∈ T, ((W i j - d) ^ 2 - W i j ^ 2)) ∧
      (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = -((S.card : ℝ) * T.card) * d ^ 2) ∧
      (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = -(blockSum W S T) ^ 2 / ((S.card : ℝ) * T.card)) := by
  classical
  dsimp only
  let d := blockSum W S T / ((S.card : ℝ) * T.card)
  have norm_sq (M : Matrix R C ℝ) : frobNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have first : frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2 =
      ∑ i ∈ S, ∑ j ∈ T, ((W i j - d) ^ 2 - W i j ^ 2) := by
    rw [norm_sq, norm_sq, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have point : ∀ i j, (W - cutMatrix S T d) i j ^ 2 - W i j ^ 2 =
        if i ∈ S then (if j ∈ T then (W i j - d)^2 - W i j^2 else 0) else 0 := by
      intro i j
      simp only [Matrix.sub_apply, cutMatrix]
      split_ifs <;> simp_all
    simp_rw [point]
    simp
  have calc_sum : (∑ i ∈ S, ∑ j ∈ T, ((W i j - d)^2 - W i j^2)) =
      -2 * d * blockSum W S T + ((S.card : ℝ) * T.card) * d^2 := by
    simp_rw [show ∀ x : ℝ, (x-d)^2-x^2 = -2*d*x+d^2 by intro x; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, blockSum]
    ring
  have hn : (S.card : ℝ) * T.card ≠ 0 := by
    have hs : 0 < S.card := Finset.card_pos.mpr hS
    have ht : 0 < T.card := Finset.card_pos.mpr hT
    positivity
  refine ⟨first, ?_, ?_⟩
  · rw [first, calc_sum]
    dsimp [d]
    field_simp
    <;> ring
  · rw [first, calc_sum]
    dsimp [d]
    field_simp
    <;> ring



#print axioms solution

