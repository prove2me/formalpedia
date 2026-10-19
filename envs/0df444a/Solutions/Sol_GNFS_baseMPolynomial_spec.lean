-- Prove2me | solution 1 for GNFS.baseMPolynomial_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:49:02.498903+00:00
-- url     : https://prove2.me/submissions/37755643-6b90-4c67-b311-40b04e386375

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial GNFS

namespace GNFSBaseM

lemma eval_sum (L : List ℕ) (m : ℤ) :
    (∑ i ∈ Finset.range L.length, C ((L.getD i 0 : ℕ) : ℤ) * X ^ i).eval m =
      Nat.ofDigits m L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons h t ih =>
    rw [List.length_cons, Finset.sum_range_succ', eval_add, Nat.ofDigits, ← ih, eval_finsetSum,
      eval_finsetSum, Finset.mul_sum, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, eval_C]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    ring

lemma coeff_sum (L : List ℕ) (i : ℕ) :
    (∑ k ∈ Finset.range L.length, C ((L.getD k 0 : ℕ) : ℤ) * X ^ k).coeff i =
      if i < L.length then ((L.getD i 0 : ℕ) : ℤ) else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

end GNFSBaseM

open GNFSBaseM in
theorem solution (n m : ℕ) (hm : 2 ≤ m) :
    (baseMPolynomial n m).eval (m : ℤ) = n ∧
      (∀ i, 0 ≤ (baseMPolynomial n m).coeff i ∧ (baseMPolynomial n m).coeff i < m) ∧
      ((baseMPolynomial n m).map (Int.castRingHom (ZMod n))).IsRoot (m : ZMod n) := by
  have heval : (baseMPolynomial n m).eval (m : ℤ) = n := by
    unfold baseMPolynomial
    rw [eval_sum, ← Nat.coe_ofDigits, Nat.ofDigits_digits]
  refine ⟨heval, fun i => ?_, ?_⟩
  · unfold baseMPolynomial
    rw [GNFSBaseM.coeff_sum]
    split_ifs with hi
    · refine ⟨Nat.cast_nonneg _, ?_⟩
      have hmem : (Nat.digits m n).getD i 0 ∈ Nat.digits m n := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact_mod_cast Nat.digits_lt_base (by omega) hmem
    · exact ⟨le_rfl, by omega⟩
  · rw [IsRoot, ← Int.cast_natCast (R := ZMod n) m, eval_intCast_map, Int.cast_id, heval]
    simp
