-- Prove2me | solution 1 for CompOT.Assignment.birkhoff_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-09T16:52:06.437975+00:00
-- url     : https://prove2.me/submissions/8a717d61-fcaa-4a03-9a2e-47beaf8902d9

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

open Finset
open scoped Pointwise

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

theorem birkhoff_extreme_points {n : ℕ} (hn : 0 < n) :
    Set.extremePoints ℝ (couplings (uniform n) (uniform n)) =
      {P : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), P = permCoupling σ} := by
  apply subset_antisymm
  · rw [couplings_uniform_eq_convexHull hn]
    exact extremePoints_convexHull_subset
  · rintro _ ⟨σ, rfl⟩
    rw [mem_extremePoints]
    refine ⟨perm_feasible σ, fun x₁ hx₁ x₂ hx₂ hσ => ?_⟩
    obtain ⟨s, t, hs, ht, hst, hP⟩ := hσ
    have hent : ∀ i j, s * x₁ i j + t * x₂ i j = permCoupling σ i j := by
      intro i j
      rw [← hP]; simp
    -- off-support entries vanish
    have hoff : ∀ i j, j ≠ σ i → x₁ i j = 0 ∧ x₂ i j = 0 := by
      intro i j hj
      have h := hent i j
      simp only [permCoupling, if_neg hj] at h
      have h1 := hx₁.1 i j
      have h2 := hx₂.1 i j
      constructor <;> nlinarith [mul_nonneg hs.le h1, mul_nonneg ht.le h2]
    -- on-support entries equal 1/n by the row sums
    have hon : ∀ (x : Matrix (Fin n) (Fin n) ℝ), x ∈ couplings (uniform n) (uniform n) →
        (∀ i j, j ≠ σ i → x i j = 0) → x = permCoupling σ := by
      intro x hx hz
      ext i j
      have hrow := hx.2.1 i
      rw [Finset.sum_eq_single (σ i) (fun b _ hb => hz i b hb) (by simp)] at hrow
      by_cases hj : j = σ i
      · subst hj; simp [permCoupling, hrow, uniform]
      · simp [permCoupling, hj, hz i j hj]
    exact ⟨hon x₁ hx₁ fun i j hj => (hoff i j hj).1, hon x₂ hx₂ fun i j hj => (hoff i j hj).2⟩

end CompOT.Assignment

open CompOT.Assignment

theorem solution {n : ℕ} (hn : 0 < n) :
    Set.extremePoints ℝ (couplings (uniform n) (uniform n)) =
      {P : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), P = permCoupling σ} :=
  CompOT.Assignment.birkhoff_extreme_points hn
