-- Prove2me | solution 1 for BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:38.341441+00:00
-- url     : https://prove2.me/submissions/d122ddb6-6bbe-4677-a531-1aeb3af65bd9

-- Generated from ChapterReconstruct.lean — solution of BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag
import Mathlib
import Definitions.Def_ChapterReconstruct
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq
open BookProof.ChapterReconstruct



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Fin n → Fin n → ℂ) (a : Fin n)
    (hU : ∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) : IsDeterministicCol U a := by

  intro l m hlm
  set C := (starRingEnd ℂ) (U m a) * U l a
  have h_C_zero : C = 0 := by
    -- By hypothesis `hU`, we know that `offDiag U a Ψz = 0` for any `z : ℂ`.
    have hz : ∀ z : ℂ, (starRingEnd ℂ) z * C + z * (starRingEnd ℂ) C = 0 := by
      intro z
      have hz : offDiag U a (fun k => if k = m then 1 else if k = l then z else 0) = (starRingEnd ℂ)
          z * C + z * (starRingEnd ℂ) C := by
        rw [ offDiag_eq ];
        simp only [mul_ite, mul_one, mul_zero, sum_ite, filter_eq', mem_univ, ↓reduceIte,
          sum_singleton, filter_ne', mem_erase, ne_eq, hlm, not_false_eq_true, and_self,
          ite_mul, zero_mul, map_one] ; ring;
        rw [ Finset.sum_eq_add ( m ) ( l ) ] <;> simp only [↓reduceIte, map_one, one_mul, hlm,
                                                   sum_const_zero,
                                                   sub_zero,
                                                   zero_mul,
                                                   add_zero,
                                                   ne_eq,
                                                   hlm.symm,
                                                   not_false_eq_true,
                                                   mem_univ,
                                                   mul_eq_zero,
                                                   map_eq_zero,
                                                   and_imp,
                                                   forall_const,
                                                   not_true_eq_false,
                                                   IsEmpty.forall_iff] ; focus (ring!);
        · simp [ mul_comm ];
        · aesop;
      rw [ ← hz, hU ];
    grind +locals;
  exact h_C_zero
