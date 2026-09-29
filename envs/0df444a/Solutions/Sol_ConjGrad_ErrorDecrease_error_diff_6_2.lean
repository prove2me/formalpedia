-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.error_diff_6_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:13:55.958017+00:00
-- url     : https://prove2.me/submissions/cab4368f-aeb0-4f6c-bfb7-fc3da2bc698a

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease

theorem aux_ed62_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have hs : Aᵀ = A := by
    have := hA.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]

theorem aux_ed62_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (i : ℕ) :
    (cgIter A k x₀ i).r = k - A *ᵥ (cgIter A k x₀ i).x ∧
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).r =
        (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r := by
  induction i with
  | zero => simp [cgIter]
  | succ i ih =>
    simp only [cgIter]
    set s := cgIter A k x₀ i with hs
    set a := cgAlpha A s with ha
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [mulVec_add, mulVec_smul, h1]
      abel
    · have hpr : s.p ⬝ᵥ (s.r - a • (A *ᵥ s.p)) = 0 := by
        by_cases hp : s.p = 0
        · rw [hp]; simp
        · have hq : 0 < s.p ⬝ᵥ (A *ᵥ s.p) := by
            have := hA.dotProduct_mulVec_pos hp
            simpa using this
          rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, h2, ha, cgAlpha]
          field_simp
          ring
      rw [add_dotProduct, smul_dotProduct, hpr, smul_zero, add_zero]

theorem aux_ed62_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (l : ℕ) :
    errorFun A h (cgIter A k x₀ l).x - errorFun A h (cgIter A k x₀ (l + 1)).x =
      cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r) := by
  obtain ⟨h1, h2⟩ := aux_ed62_inv A hA k x₀ l
  simp only [cgIter]
  set s := cgIter A k x₀ l with hs
  set a := cgAlpha A s with ha
  have he : A *ᵥ (h - s.x) = s.r := by rw [mulVec_sub, hh, h1]
  have hsym : (h - s.x) ⬝ᵥ (A *ᵥ s.p) = s.p ⬝ᵥ (A *ᵥ (h - s.x)) :=
    aux_ed62_symm A hA _ _
  have hsub : h - (s.x + a • s.p) = (h - s.x) - a • s.p := by abel
  unfold errorFun
  rw [hsub, mulVec_sub A (h - s.x) (a • s.p), mulVec_smul, he]
  rw [he] at hsym
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    at hsym ⊢
  have key : a * (s.p ⬝ᵥ (A *ᵥ s.p)) = s.r ⬝ᵥ s.r ∨ a = 0 := by
    by_cases hq : s.p ⬝ᵥ (A *ᵥ s.p) = 0
    · right; rw [ha, cgAlpha, hq, div_zero]
    · left; rw [ha, cgAlpha]; field_simp
  rcases key with key | key
  · have : a * (a * (s.p ⬝ᵥ (A *ᵥ s.p))) = a * (s.r ⬝ᵥ s.r) := by rw [key]
    linear_combination a * hsym + 2 * a * h2 - this
  · rw [key]; ring

end ConjGrad.ErrorDecrease

open ConjGrad.ErrorDecrease
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i j : ℕ) (hij : i < j) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ j).x =
      ∑ l ∈ Finset.Ico i j,
        cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r) := by
  induction j, hij.le using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ← aux_ed62_step A hA k x₀ h hh m]
    rcases hm.lt_or_eq with hlt | heq
    · rw [← ih hlt]; ring
    · subst heq; simp
