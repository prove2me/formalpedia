-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_even_flip
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:04:55.858141+00:00
-- url     : https://prove2.me/submissions/828ad45d-b2ea-4b7b-b1d4-8278e476e761

-- Generated from ChapterFreeFieldBornSignOrientationCard.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_even_flip
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
open BookProof.ChapterFreeFieldBornSignOrientationCard



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    Nat.card {b : Fin (n + 1) → Bool // Even (flipCount b)} = 2 ^ n := by

  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  have h_gen_fun : (∑ i : Fin (n + 1) → Bool, (-1 : ℝ) ^ flipCount i) = 0 := by
    have h_incl_excl :
        ∑ i : Fin (n + 1) → Bool,
            (-1 : ℝ) ^ (Finset.univ.filter fun k => i k = true).card =
          ∏ _k : Fin (n + 1), ∑ b : Bool, (-1 : ℝ) ^ (if b then 1 else 0) := by
      rw [Finset.prod_sum]
      refine Finset.sum_bij (fun i ?_ => fun k _ => i k) ?_ ?_ ?_ ?_ <;> simp only [Finset.mem_univ,
          Fintype.univ_bool, Finset.mem_pi, Finset.mem_insert, Finset.mem_singleton,
              Bool.eq_true_or_eq_false_self, imp_self, implies_true, forall_const, exists_const,
                  pow_ite, pow_one, pow_zero, Finset.prod_attach_univ]
      · simp [funext_iff]
      · exact fun b => ⟨fun k => b k (Finset.mem_univ k), rfl⟩
      · intro a
        rw [Finset.prod_ite]
        aesop
    convert h_incl_excl using 1
    · simp [flipCount]
    · norm_num [Finset.prod_const, Finset.card_univ]
  have h_eq :
      (∑ i : Fin (n + 1) → Bool, (if Even (flipCount i) then 1 else 0) : ℝ) -
          (∑ i : Fin (n + 1) → Bool, (if Odd (flipCount i) then 1 else 0) : ℝ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Eq.trans (Finset.sum_congr rfl fun _ _ => by aesop) h_gen_fun
  simp_all [sub_eq_iff_eq_add]
  have hcard := Finset.card_add_card_compl
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => Even (flipCount x))
  simp_all [pow_succ']
  linarith
