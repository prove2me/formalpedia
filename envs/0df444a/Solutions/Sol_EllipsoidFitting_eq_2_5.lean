-- Prove2me | solution 1 for EllipsoidFitting.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:52:51.739848+00:00
-- url     : https://prove2.me/submissions/2ace3417-0663-4de8-bb33-23c86fc8dbad

import Mathlib
import Definitions.Def_EllipsoidFitting_matA

set_option autoImplicit false

open Matrix

namespace EllipsoidFitting.Aux_EF

theorem sym_sum {d : ℕ} (X : Fin d → Fin d → ℝ) (hX : ∀ a b, X a b = X b a) :
    (∑ a, ∑ b, if a = b then 0 else X a b) = 2 * ∑ a, ∑ b, if a < b then X a b else 0 := by
  have hsplit : ∀ a b : Fin d, (if a = b then 0 else X a b) =
      (if a < b then X a b else 0) + (if b < a then X a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [if_neg (ne_of_lt h), if_pos h, if_neg (not_lt_of_gt h), add_zero]
    · subst h; simp
    · rw [if_neg (ne_of_gt h), if_neg (not_lt_of_gt h), if_pos h, zero_add]
  have hswap : (∑ a : Fin d, ∑ b : Fin d, if b < a then X a b else 0) =
      ∑ a : Fin d, ∑ b : Fin d, if a < b then X a b else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hX]
  simp only [hsplit, Finset.sum_add_distrib, hswap]
  ring

end EllipsoidFitting.Aux_EF

open EllipsoidFitting EllipsoidFitting.Aux_EF in
theorem solution {m d : ℕ} (v : Fin m → Fin d → ℝ) :
    gram v = matA v + matB v ∧
      ∀ i j, i ≠ j →
        Malpha v i j = 2 * ∑ a, ∑ b, if a < b then v i a * v i b * v j a * v j b else 0 := by
  have hdc : (d : ℝ) * (1 / (d : ℝ)) ^ 2 = 1 / (d : ℝ) := by
    rcases eq_or_ne (d : ℝ) 0 with h | h
    · simp [h]
    · field_simp
  have hnorm : ∀ i, v i ⬝ᵥ v i = ∑ a, v i a ^ 2 := by
    intro i; simp only [dotProduct, sq]
  constructor
  · ext i j
    simp only [EllipsoidFitting.gram, matA, matB, Malpha, Mbeta, MD, eta, constraintMap, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, vecMulVec_apply, one_mulVec,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      ring
    · simp only [if_neg hij]
      have e1 : (v i ⬝ᵥ v j) ^ 2 = ∑ a, v i a ^ 2 * v j a ^ 2 +
          ∑ a, ∑ b, (if a = b then 0 else v i a * v i b * v j a * v j b) := by
        rw [dotProduct, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have : ∀ b, v i a * v j a * (v i b * v j b) =
            (if a = b then v i a ^ 2 * v j a ^ 2 else 0) +
              (if a = b then 0 else v i a * v i b * v j a * v j b) := by
          intro b
          split_ifs with h
          · subst h; ring
          · ring
        rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      have e2 : ∑ a, (v i a ^ 2 - 1 / (d : ℝ)) * (v j a ^ 2 - 1 / (d : ℝ)) =
          ∑ a, v i a ^ 2 * v j a ^ 2 - 1 / (d : ℝ) * ∑ a, v i a ^ 2 -
            1 / (d : ℝ) * ∑ a, v j a ^ 2 + (d : ℝ) * (1 / (d : ℝ)) ^ 2 := by
        have : ∀ a, (v i a ^ 2 - 1 / (d : ℝ)) * (v j a ^ 2 - 1 / (d : ℝ)) =
            v i a ^ 2 * v j a ^ 2 - 1 / (d : ℝ) * v i a ^ 2 - 1 / (d : ℝ) * v j a ^ 2 +
              (1 / (d : ℝ)) ^ 2 := by intro a; ring
        rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [e1, e2, hnorm i, hnorm j, hdc]
      ring
  · intro i j hij
    simp only [Malpha, Matrix.of_apply, if_neg hij]
    exact sym_sum (fun a b => v i a * v i b * v j a * v j b) (fun a b => by ring)
