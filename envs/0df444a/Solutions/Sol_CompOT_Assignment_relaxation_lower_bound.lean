-- Prove2me | solution 1 for CompOT.Assignment.relaxation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-09T16:52:05.654072+00:00
-- url     : https://prove2.me/submissions/688cbaba-22a2-4342-b4a1-b96ccd2dd953

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

open Finset
open scoped Pointwise

theorem assignment_cost {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    frob C (permCoupling σ) = assignmentCost C σ := by
  simp only [frob, permCoupling, assignmentCost, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem perm_feasible {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permCoupling σ ∈ couplings (uniform n) (uniform n) := by
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · unfold permCoupling
    split_ifs <;> positivity
  · simp [permCoupling, uniform]
  · simp only [permCoupling, uniform]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (by rw [h]; simp)
    · simp

theorem convex_couplings {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Convex ℝ (couplings a b) := by
  rintro x ⟨hx0, hxr, hxc⟩ y ⟨hy0, hyr, hyc⟩ s t hs ht hst
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have := hx0 i j; have := hy0 i j; positivity
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hxr, hyr]
    rw [← add_mul, hst, one_mul]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hxc, hyc]
    rw [← add_mul, hst, one_mul]

theorem couplings_uniform_eq_convexHull {n : ℕ} (hn : 0 < n) :
    couplings (uniform n) (uniform n) =
      convexHull ℝ {P : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), P = permCoupling σ} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply subset_antisymm
  · intro Q hQ
    obtain ⟨h0, hr, hc⟩ := hQ
    have hM : (n : ℝ) • Q ∈ doublyStochastic ℝ (Fin n) := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
      · simp only [Matrix.smul_apply, smul_eq_mul]
        exact mul_nonneg hn'.le (h0 i j)
      · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hr, uniform]
        field_simp
      · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hc, uniform]
        field_simp
    have hM' : (n : ℝ) • Q ∈ convexHull ℝ {x : Matrix (Fin n) (Fin n) ℝ |
        ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} := by
      rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hM
    have hQeq : Q = (1 / (n : ℝ)) • ((n : ℝ) • Q) := by
      rw [smul_smul, one_div, inv_mul_cancel₀ hn'.ne', one_smul]
    rw [hQeq]
    have hset : (1 / (n : ℝ)) • {x : Matrix (Fin n) (Fin n) ℝ |
        ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} =
        {P : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), P = permCoupling σ} := by
      ext P
      simp only [Set.mem_smul_set, Set.mem_setOf_eq]
      constructor
      · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
        refine ⟨σ, ?_⟩
        ext i j
        simp [permCoupling, Equiv.toPEquiv_apply, eq_comm]
      · rintro ⟨σ, rfl⟩
        refine ⟨_, ⟨σ, rfl⟩, ?_⟩
        ext i j
        simp [permCoupling, Equiv.toPEquiv_apply, eq_comm]
    rw [← hset, convexHull_smul]
    exact Set.smul_mem_smul_set hM'
  · apply convexHull_min _ (convex_couplings _ _)
    rintro _ ⟨σ, rfl⟩
    exact perm_feasible σ

theorem frob_convex_comb {n m : ℕ} (C x y : Matrix (Fin n) (Fin m) ℝ) (s t : ℝ) :
    frob C (s • x + t • y) = s * frob C x + t * frob C y := by
  simp only [frob, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem proposition_2_1 {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ∃ σ : Equiv.Perm (Fin n),
      IsOptimalCoupling C (uniform n) (uniform n) (permCoupling σ) ∧
      ∀ τ : Equiv.Perm (Fin n), assignmentCost C σ ≤ assignmentCost C τ := by
  obtain ⟨σ, -, hσ⟩ := Finset.univ.exists_min_image (assignmentCost C) Finset.univ_nonempty
  refine ⟨σ, ⟨perm_feasible σ, fun Q hQ => ?_⟩, fun τ => hσ τ (Finset.mem_univ τ)⟩
  rw [couplings_uniform_eq_convexHull hn] at hQ
  have hH : Convex ℝ {M : Matrix (Fin n) (Fin n) ℝ | frob C (permCoupling σ) ≤ frob C M} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [frob_convex_comb]
    have h1 := mul_le_mul_of_nonneg_left hx hs
    have h2 := mul_le_mul_of_nonneg_left hy ht
    have h3 : s * frob C (permCoupling σ) + t * frob C (permCoupling σ) =
        frob C (permCoupling σ) := by rw [← add_mul, hst, one_mul]
    linarith
  refine convexHull_min ?_ hH hQ
  rintro _ ⟨τ, rfl⟩
  simp only [Set.mem_setOf_eq, assignment_cost]
  exact hσ τ (Finset.mem_univ τ)

theorem relaxation_lower_bound {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    otCost C (uniform n) (uniform n) ≤ assignmentMin C := by
  obtain ⟨σ, ⟨-, hσ⟩, -⟩ := proposition_2_1 hn C
  have hbdd : BddBelow {v : ℝ | ∃ P ∈ couplings (uniform n) (uniform n), v = frob C P} := by
    refine ⟨frob C (permCoupling σ), ?_⟩
    rintro v ⟨P, hP, rfl⟩
    exact hσ P hP
  refine le_csInf ⟨assignmentCost C 1, 1, rfl⟩ ?_
  rintro v ⟨τ, rfl⟩
  rw [← assignment_cost]
  exact csInf_le hbdd ⟨permCoupling τ, perm_feasible τ, rfl⟩

end CompOT.Assignment

open CompOT.Assignment

theorem solution {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    otCost C (uniform n) (uniform n) ≤ assignmentMin C :=
  CompOT.Assignment.relaxation_lower_bound hn C
