-- Prove2me | solution 1 for FermionModewise.eq_20b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:51:02.194888+00:00
-- url     : https://prove2.me/submissions/e1030583-1866-4244-8ebe-b196411ea0f4

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace Aux_FermionModewise_eq_20b

open FermionModewise

theorem hW {μ : Type} [DecidableEq μ] (lam : ℝ) :
    williamson (fun _ : μ => lam) = lam • williamson (fun _ : μ => (1 : ℝ)) := by
  ext p q
  simp only [williamson, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem hJJ {μ : Type} [Fintype μ] [DecidableEq μ] :
    williamson (fun _ : μ => (1 : ℝ)) * williamson (fun _ : μ => (1 : ℝ)) = -1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [williamson, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq, one_mul, ite_mul, zero_mul, mul_ite,
    mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.sum_univ_two]
  by_cases hab : a = b
  · subst hab
    fin_cases i <;> fin_cases j <;> simp [J2]
  · simp [hab, Finset.sum_add_distrib, Finset.sum_ite_eq']

end Aux_FermionModewise_eq_20b

open FermionModewise in
theorem solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam lam0 : ℝ) (hlam : 0 ≤ lam) (hlam0 : 0 ≤ lam0) (hlam_ne : lam ≠ 0)
    (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) *
        Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) =
      (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    williamson (fun _ : α => (1 : ℝ)) * K * williamson (fun _ : β => (1 : ℝ)) = K := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul] at h
  obtain ⟨-, hB, -, -⟩ := fromBlocks_inj.mp h
  rw [Aux_FermionModewise_eq_20b.hW (μ := α) lam, Aux_FermionModewise_eq_20b.hW (μ := β) lam,
    smul_zero, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, smul_eq_zero] at hB
  rcases hB with hB | hB
  · exact absurd hB hlam_ne
  · have hA : williamson (fun _ : α => (1 : ℝ)) * K = -(K * williamson (fun _ : β => (1 : ℝ))) :=
      eq_neg_of_add_eq_zero_left hB
    rw [hA, Matrix.neg_mul, Matrix.mul_assoc, Aux_FermionModewise_eq_20b.hJJ, Matrix.mul_neg,
      Matrix.mul_one, neg_neg]
