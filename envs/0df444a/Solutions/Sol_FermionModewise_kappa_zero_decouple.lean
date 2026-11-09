-- Prove2me | solution 1 for FermionModewise.kappa_zero_decouple
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:18:24.064076+00:00
-- url     : https://prove2.me/submissions/f8c9008b-8385-4236-92e3-a20cf7e35278

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace Aux_FermionModewise_kzd
open FermionModewise

theorem wsq {γ : Type} [Fintype γ] [DecidableEq γ] (lam0 : ℝ) :
    williamson (fun _ : γ => lam0) * williamson (fun _ : γ => lam0) =
      (-(lam0 ^ 2)) • (1 : Matrix (γ × Fin 2) (γ × Fin 2) ℝ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [williamson, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab
      fin_cases i <;> fin_cases j <;> simp [J2, Fin.sum_univ_two, Matrix.one_apply] <;> ring
    · simp [hab, Matrix.one_apply]
  · intro c _ hca
    simp [Ne.symm hca]
  · intro h; exact absurd (Finset.mem_univ a) h

end Aux_FermionModewise_kzd

open FermionModewise in
theorem solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam0 : ℝ) (hlam0 : 0 ≤ lam0) (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : α => lam0) K (-Kᵀ) (williamson fun _ : β => lam0) *
        Matrix.fromBlocks (williamson fun _ : α => lam0) K (-Kᵀ) (williamson fun _ : β => lam0) =
      (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    K = 0 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero,
    Matrix.fromBlocks_inj] at h
  have h1 := h.1
  rw [Aux_FermionModewise_kzd.wsq, Matrix.mul_neg, add_neg_eq_iff_eq_add, left_eq_add] at h1
  -- h1 : K * Kᵀ = 0
  ext p q
  have hpp := congrFun (congrFun h1 p) p
  rw [Matrix.mul_apply] at hpp
  simp only [Matrix.transpose_apply, Matrix.zero_apply] at hpp
  have hnn : ∀ r ∈ Finset.univ, 0 ≤ K p r * K p r := fun r _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hpp q (Finset.mem_univ q)
  simpa using mul_self_eq_zero.mp this
