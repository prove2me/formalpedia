-- Prove2me | solution 1 for EastinKnill.Transversal.part_detection
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:10:24.769507+00:00
-- url     : https://prove2.me/submissions/f95bb140-7d32-4097-8127-336b653341d7

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix
open EastinKnill.Transversal

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ι → Type*} [∀ j, Fintype (γ j)]
  [∀ j, DecidableEq (γ j)]

lemma localOp_applyX (j : ι) (E : Matrix (γ j) (γ j) ℂ) (x y : ∀ k, γ k) :
    localOp γ j E x y = E (x j) (y j) *
      ∏ k ∈ Finset.univ.erase j, (if x k = y k then (1 : ℂ) else 0) := by
  unfold localOp prodOp
  rw [Matrix.of_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk), Matrix.one_apply]
end

section
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
  {α : β → ι → Type*} [∀ b j, Fintype (α b j)] [∀ b j, DecidableEq (α b j)]

noncomputable def bcX (Q : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ) :
    Matrix (∀ j, ∀ b, α b j) (∀ j, ∀ b, α b j) ℂ :=
  Matrix.of fun x y => ∏ b, Q b (fun j => x j b) (fun j => y j b)

lemma bc_mulX (Q R : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ) :
    bcX Q * bcX R = bcX (fun b => Q b * R b) := by
  ext x z
  simp only [bcX, Matrix.mul_apply, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  exact (Fintype.sum_equiv (Equiv.piComm fun j b => α b j) _ _ (fun y => rfl))

lemma bc_smulX (c : β → ℂ) (Q : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ) :
    bcX (fun b => c b • Q b) = (∏ b, c b) • bcX Q := by
  ext x y
  simp [bcX, Finset.prod_mul_distrib]

lemma local_prodX (j : ι) (e : ∀ b, Matrix (α b j) (α b j) ℂ) :
    localOp (fun j => ∀ b, α b j) j (Matrix.of fun u v => ∏ b, e b (u b) (v b)) =
      bcX (fun b => localOp (α b) j (e b)) := by
  ext x y
  simp only [bcX, Matrix.of_apply, localOp_applyX, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases h : x k = y k
  · simp [h]
  · rw [if_neg h]
    obtain ⟨b, hb⟩ : ∃ b, x k b ≠ y k b := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact (Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])).symm
end

theorem solution {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    {α : β → ι → Type*} [∀ b j, Fintype (α b j)] [∀ b j, DecidableEq (α b j)]
    (P : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ)
    (hP : ∀ b, IsCodeProjector (P b)) (hdet : ∀ b, IsLocalErrorDetecting (P b)) :
    IsLocalErrorDetecting (α := fun j => ∀ b, α b j) (blockCode α P) := by
  intro j E
  have hbc : blockCode α P = bcX P := rfl
  -- matrix units
  let U : (∀ b, α b j) → (∀ b, α b j) → Matrix (∀ b, α b j) (∀ b, α b j) ℂ := fun u v =>
    Matrix.of fun s t => ∏ b, Matrix.single (u b) (v b) (1 : ℂ) (s b) (t b)
  have hE : E = ∑ u, ∑ v, E u v • U u v := by
    ext s t
    simp only [U, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have : ∀ u v, (∏ b, Matrix.single (u b) (v b) (1 : ℂ) (s b) (t b)) =
        if u = s ∧ v = t then 1 else 0 := by
      intro u v
      simp only [Matrix.single_apply]
      rw [Fintype.prod_ite_zero]
      simp only [Finset.prod_const_one]
      congr 1
      exact propext ⟨fun h => ⟨funext fun b => (h b).1, funext fun b => (h b).2⟩,
        fun h b => ⟨congrFun h.1 b, congrFun h.2 b⟩⟩
    simp only [this, mul_ite, mul_one, mul_zero, ite_and]
    simp
  have hlin : ∀ (c : (∀ b, α b j) → (∀ b, α b j) → ℂ),
      localOp (fun j => ∀ b, α b j) j (∑ u, ∑ v, c u v • U u v) =
        ∑ u, ∑ v, c u v • localOp (fun j => ∀ b, α b j) j (U u v) := by
    intro c
    ext x y
    simp only [localOp_applyX, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
      mul_assoc]
  choose cc hcc using fun b => hdet b j
  refine ⟨∑ u, ∑ v, E u v * ∏ b, cc b (Matrix.single (u b) (v b) 1), ?_⟩
  rw [hbc]
  have hL := hlin (fun u v => E u v)
  rw [← hE] at hL
  rw [hL]
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_smul]
  congr 1
  have : U u v = Matrix.of fun s t => ∏ b, Matrix.single (u b) (v b) (1 : ℂ) (s b) (t b) := rfl
  rw [this, local_prodX, bc_mulX, bc_mulX]
  rw [show (fun b => P b * localOp (α b) j (Matrix.single (u b) (v b) 1) * P b) =
      fun b => cc b (Matrix.single (u b) (v b) 1) • P b from funext fun b => hcc b _]
  exact bc_smulX _ _
