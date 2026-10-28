-- Prove2me | solution 1 for EastinKnill.Transversal.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:11:11.211097+00:00
-- url     : https://prove2.me/submissions/3dd3758c-4a26-457f-94ef-df32ab47c1dd

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix
open EastinKnill.Transversal
open scoped ComplexOrder

lemma invX {n : Type*} [Fintype n] [DecidableEq n] (P U : Matrix n n ℂ)
    (hPh : Pᴴ = P) (hPP : P * P = P) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (h : (1 - P) * U * P = 0) : (1 - P) * Uᴴ * P = 0 := by
  have hUP : P * U * P = U * P := by
    have := h; rw [sub_mul, sub_mul, one_mul] at this; exact (sub_eq_zero.mp this).symm
  have hPQ : P * (U * P * Uᴴ) = U * P * Uᴴ := by
    calc P * (U * P * Uᴴ) = (P * U * P) * Uᴴ := by simp only [mul_assoc]
      _ = U * P * Uᴴ := by rw [hUP]
  have hQh : (U * P * Uᴴ)ᴴ = U * P * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPh,
      mul_assoc]
  have hQP : (U * P * Uᴴ) * P = U * P * Uᴴ := by
    have := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, hQh, hPh] at this
  have hQQ : (U * P * Uᴴ) * (U * P * Uᴴ) = U * P * Uᴴ := by
    calc U * P * Uᴴ * (U * P * Uᴴ) = U * (P * (Uᴴ * U) * P) * Uᴴ := by simp only [mul_assoc]
      _ = U * P * Uᴴ := by rw [h1, mul_one, hPP]
  set Q := U * P * Uᴴ with hQ
  have hRh : (P - Q)ᴴ = P - Q := by rw [Matrix.conjTranspose_sub, hPh, hQh]
  have hRR : (P - Q) * (P - Q) = P - Q := by
    rw [sub_mul, mul_sub, mul_sub, hPP, hPQ, hQP, hQQ]; abel
  have htr : ((P - Q)ᴴ * (P - Q)).trace = 0 := by
    rw [hRh, hRR, Matrix.trace_sub, hQ, Matrix.trace_mul_comm, ← mul_assoc, h1, one_mul, sub_self]
  have hR0 : P - Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  have hQe : U * P * Uᴴ = P := (sub_eq_zero.mp hR0).symm
  have hcomm : U * P = P * U := by
    calc U * P = U * P * (Uᴴ * U) := by rw [h1, mul_one]
      _ = (U * P * Uᴴ) * U := by simp only [mul_assoc]
      _ = P * U := by rw [hQe]
  have hcomm' : Uᴴ * P = P * Uᴴ := by
    calc Uᴴ * P = Uᴴ * P * (U * Uᴴ) := by rw [h2, mul_one]
      _ = Uᴴ * (P * U) * Uᴴ := by simp only [mul_assoc]
      _ = Uᴴ * (U * P) * Uᴴ := by rw [hcomm]
      _ = P * Uᴴ := by rw [← mul_assoc, h1, one_mul]
  rw [mul_assoc, hcomm', ← mul_assoc, sub_mul, one_mul, hPP, sub_self, zero_mul]

theorem solution {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : IsCodeProjector P) (A : Subgroup (Matrix.unitaryGroup n ℂ))
    (hA : IsClosed (A : Set (Matrix.unitaryGroup n ℂ))) :
    ∃ B : Subgroup (Matrix.unitaryGroup n ℂ),
      (B : Set (Matrix.unitaryGroup n ℂ)) =
        (A : Set (Matrix.unitaryGroup n ℂ)) ∩ {U | IsLogical P (U : Matrix n n ℂ)} ∧
      IsClosed (B : Set (Matrix.unitaryGroup n ℂ)) := by
  obtain ⟨hPh, hPP⟩ := hP
  have hPh' : Pᴴ = P := hPh
  let L : Subgroup (Matrix.unitaryGroup n ℂ) :=
    { carrier := {U : Matrix.unitaryGroup n ℂ | IsLogical P (U : Matrix n n ℂ)},
      mul_mem' := by
        intro U V hU hV
        simp only [Set.mem_setOf_eq, IsLogical] at hU hV ⊢
        have hVP : V.1 * P = P * V.1 * P := by
          rw [sub_mul, sub_mul, one_mul] at hV; exact sub_eq_zero.mp hV
        show (1 - P) * (U.1 * V.1) * P = 0
        calc (1 - P) * (U.1 * V.1) * P = (1 - P) * U.1 * (V.1 * P) := by simp only [mul_assoc]
          _ = ((1 - P) * U.1 * P) * V.1 * P := by rw [hVP]; simp only [mul_assoc]
          _ = 0 := by rw [hU, zero_mul, zero_mul]
      one_mem' := by
        simp only [Set.mem_setOf_eq, IsLogical]
        show (1 - P) * 1 * P = 0
        rw [mul_one, sub_mul, one_mul, hPP, sub_self]
      inv_mem' := by
        intro U hU
        simp only [Set.mem_setOf_eq, IsLogical] at hU ⊢
        show (1 - P) * (star U.1) * P = 0
        exact invX P U.1 hPh' hPP (Matrix.UnitaryGroup.star_mul_self U)
          (Matrix.mem_unitaryGroup_iff.mp U.2) hU }
  refine ⟨A ⊓ L, rfl, ?_⟩
  have hLc : IsClosed ({U : Matrix.unitaryGroup n ℂ | IsLogical P (U : Matrix n n ℂ)}) := by
    have : Continuous fun U : Matrix.unitaryGroup n ℂ => (1 - P) * (U : Matrix n n ℂ) * P :=
      (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
    exact isClosed_singleton.preimage this
  exact hA.inter hLc
