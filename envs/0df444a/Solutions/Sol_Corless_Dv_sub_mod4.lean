-- Prove2me | solution 1 for Corless.Dv_sub_mod4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:37.230315+00:00
-- url     : https://prove2.me/submissions/d6120890-3eab-426a-bdb8-24ef2c6cf4e8

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_sub_eq
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_parity
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s t : ℕ → ℤ} {M : ℕ} (hs : IsSign s M) (ht : IsSign t M) (δ : ℕ → ℤ)
    (hδ : ∀ j, j + 1 < M → s j - t j = 2 * δ j) :
    ∃ R : ℤ[X], Dv s M - Dv t M
      = 2 * ∑ j ∈ range (M - 1), C (δ j) * X * f j * f (M - 2 - j) + 4 * R := by
  rw [Dv_sub_eq]
  have key : ∀ j, j + 1 < M → ∃ R : ℤ[X],
      C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j)
        = 2 * (C (δ j) * X * f j * f (M - 2 - j)) + 4 * R := by
    intro j hj
    obtain ⟨A, hA⟩ := Dv_parity j (s := hyb s t j) fun i hi => by
      simpa only [hyb, if_pos (show i < j by omega)] using hs i (by omega)
    obtain ⟨B, hB⟩ := Dv_parity (M - 2 - j) (s := fun i => hyb s t j (i + j + 2)) fun i hi => by
      simpa only [hyb, if_neg (show ¬i + j + 2 < j by omega)] using ht (i + j + 2) (by omega)
    refine ⟨C (δ j) * X * (A * f (M - 2 - j) + f j * B + 2 * A * B), ?_⟩
    rw [hA, hB, hδ j hj, C_mul, show (C (2 : ℤ) : ℤ[X]) = 2 by simp]
    ring
  let R (j : ℕ) := if hj : j + 1 < M then (key j hj).choose else 0
  refine ⟨∑ j ∈ range (M - 1), R j, ?_⟩
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j + 1 < M := by simpa [Finset.mem_range, Nat.lt_sub_iff_add_lt] using hj
  simpa only [R, dif_pos hj'] using (key j hj').choose_spec
end Corless
