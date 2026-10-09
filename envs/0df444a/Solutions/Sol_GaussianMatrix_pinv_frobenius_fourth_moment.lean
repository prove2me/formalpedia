-- Prove2me | solution 1 for GaussianMatrix.pinv_frobenius_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:31:57.549104+00:00
-- url     : https://prove2.me/submissions/e5c09cb5-e4ef-4836-8b12-b49e5403a256

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_sq_moment
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_prod_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Deterministic identity: `‖G†‖_F² = tr((G Gᵀ)⁻¹)` for every real matrix `G`
(both sides vanish when `G Gᵀ` is singular, by Mathlib's convention `A⁻¹ = 0`). -/
theorem pf4_frobSq_pinvR_eq_trace_inv {r k : ℕ} (G : Matrix (Fin r) (Fin k) ℝ) :
    frobSq (pinvR G) = ∑ i, (G * Gᵀ)⁻¹ i i := by
  set A : Matrix (Fin r) (Fin r) ℝ := G * Gᵀ with hA
  set M : Matrix (Fin r) (Fin r) ℝ := A⁻¹ with hM
  have hAt : Aᵀ = A := by rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMt : Mᵀ = M := by rw [hM, Matrix.transpose_nonsing_inv, hAt]
  have hkey : (pinvR G)ᵀ * pinvR G = M := by
    unfold pinvR
    rw [← hA, ← hM, Matrix.transpose_mul, Matrix.transpose_transpose, hMt]
    by_cases h : IsUnit A.det
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, ← hA, hM, Matrix.mul_nonsing_inv A h,
        Matrix.mul_one]
    · have h0 : M = 0 := by rw [hM]; exact Matrix.nonsing_inv_apply_not_isUnit A h
      rw [h0]; simp
  have htr : frobSq (pinvR G) = Matrix.trace ((pinvR G)ᵀ * pinvR G) := by
    unfold frobSq Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [sq]
  rw [htr, hkey]
  rfl

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)) ^ 2) (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ^ 2 ∂(gaussianMatrix r k)
      = ((r : ℝ) ^ 2 * ((k : ℝ) - r) - 2 * r * ((r : ℝ) - 1))
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)) ^ 2)
      = fun G => ∑ i, ∑ j, M G i i * M G j j := by
    funext G
    rw [pf4_frobSq_pinvR_eq_trace_inv, sq, Finset.sum_mul_sum]
  -- each term `E[Mᵢᵢ Mⱼⱼ]`
  have hterm : ∀ i j : Fin r, Integrable (fun G => M G i i * M G j j) (gaussianMatrix r k) ∧
      ∫ G, M G i i * M G j j ∂(gaussianMatrix r k)
        = if i = j then 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          else ((k : ℝ) - r - 2) / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      obtain ⟨h1, h2⟩ := inverse_wishart_diag_sq_moment hrk i
      simp only [if_true, hM]
      simp only [← sq]
      exact ⟨h1, h2⟩
    · rw [if_neg hij]
      exact inverse_wishart_diag_prod_moment hrk i j hij
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hterm _ j).1, fun i j => (hterm i j).2]
  -- count the diagonal and off-diagonal terms
  have hcount : ∀ (a b : ℝ), (∑ i : Fin r, ∑ j : Fin r, if i = j then a else b)
      = r * a + ((r : ℝ) * r - r) * b := by
    intro a b
    have : ∀ i : Fin r, (∑ j : Fin r, if i = j then a else b) = a + ((r : ℝ) - 1) * b := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      rw [if_pos rfl, Finset.sum_congr rfl (fun j hj => if_neg (Ne.symm (Finset.ne_of_mem_erase hj))),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos r with h | h
      · exact (Fin.elim0 (h ▸ i))
      · rw [Nat.cast_sub (by omega)]; push_cast; ring
    simp_rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount]
  have hx : (4 : ℝ) ≤ (k : ℝ) - r := by
    have : ((r + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at this; linarith
  have h1 : (k : ℝ) - r ≠ 0 := by linarith
  have h2 : (k : ℝ) - r - 1 ≠ 0 := by linarith
  have h3 : (k : ℝ) - r - 3 ≠ 0 := by linarith
  field_simp
  ring
