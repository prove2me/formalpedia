-- Prove2me | solution 1 for GNFS.exists_ringOfIntegers_ne_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:51:28.786728+00:00
-- url     : https://prove2.me/submissions/81ca4a00-1012-425c-a587-222f1fa28e82

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

namespace GNFSExample

noncomputable def θ : ℂ := Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)

lemma θ_sq : θ ^ 2 = -3 := by
  unfold θ
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  push_cast; ring

lemma θ_re : θ.re = 0 := by simp [θ]

/-- The subalgebra `{a + bθ : a, b ∈ ℤ}`. -/
noncomputable def S : Subalgebra ℤ ℂ where
  carrier := {z | ∃ a b : ℤ, z = a + b * θ}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - 3 * b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination (b * d : ℂ) * θ_sq
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  algebraMap_mem' := by
    intro r
    exact ⟨r, 0, by simp⟩

lemma not_mem_S : (1 + θ) / 2 ∉ S := by
  rintro ⟨a, b, h⟩
  have h1 := congrArg Complex.re h
  simp only [Complex.div_re, Complex.add_re, Complex.one_re, θ_re, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero] at h1
  norm_num at h1
  have : (2 : ℝ) * a = 1 := by linarith
  have : (2 : ℤ) * a = 1 := by exact_mod_cast this
  omega

end GNFSExample

open GNFSExample in
theorem solution :
    ∃ (f : ℤ[X]) (θ : ℂ), f.Monic ∧ Irreducible f ∧ aeval θ f = 0 ∧
      ∃ x : ℂ, x ∈ ℚ⟮θ⟯ ∧ IsIntegral ℤ x ∧ x ∉ Algebra.adjoin ℤ ({θ} : Set ℂ) := by
  have hmon : (X ^ 2 + C 3 : ℤ[X]).Monic := monic_X_pow_add_C 3 (by norm_num)
  have hdeg : (X ^ 2 + C 3 : ℤ[X]).natDegree = 2 := by
    rw [natDegree_X_pow_add_C]
  refine ⟨X ^ 2 + C 3, GNFSExample.θ, hmon, ?_, ?_, (1 + GNFSExample.θ) / 2, ?_, ?_, ?_⟩
  · rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    apply Multiset.eq_zero_of_forall_notMem
    intro r hr
    rw [mem_roots hmon.ne_zero, IsRoot, eval_add, eval_pow, eval_X, eval_C] at hr
    nlinarith [sq_nonneg r]
  · rw [aeval_add, aeval_X_pow, aeval_C, θ_sq]; simp
  · have hθ : GNFSExample.θ ∈ ℚ⟮GNFSExample.θ⟯ := mem_adjoin_simple_self ℚ _
    have h2 : (2 : ℂ) ∈ ℚ⟮GNFSExample.θ⟯ := by
      have := (ℚ⟮GNFSExample.θ⟯).algebraMap_mem (2 : ℚ)
      simpa using this
    exact div_mem (add_mem (one_mem _) hθ) h2
  · refine ⟨X ^ 2 - X + 1, ?_, ?_⟩
    · have : (X ^ 2 - X + 1 : ℤ[X]) = X ^ 2 + (C (-1) * X + C 1) := by
        simp only [map_neg, map_one, neg_mul, one_mul]; ring
      rw [this]
      exact monic_X_pow_add (by
        refine (degree_add_le _ _).trans_lt ?_
        rw [max_lt_iff]
        constructor
        · exact (degree_C_mul_X_le _).trans_lt (by norm_num)
        · exact (degree_C_le).trans_lt (by norm_num))
    · simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
      linear_combination (1 / 4 : ℂ) * θ_sq
  · intro hx
    have hle : Algebra.adjoin ℤ ({GNFSExample.θ} : Set ℂ) ≤ S := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨0, 1, by simp⟩
    exact not_mem_S (hle hx)
