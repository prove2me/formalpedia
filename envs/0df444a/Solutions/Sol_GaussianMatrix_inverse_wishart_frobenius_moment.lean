-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_frobenius_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:24:13.957592+00:00
-- url     : https://prove2.me/submissions/6662d64f-e013-40ec-babc-5cf8786351e3

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_sq_moment
import Theorems.Thm_GaussianMatrix_inverse_wishart_offdiag_sq_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      (gaussianMatrix r k) ∧
    ∫ G, frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k)
      = (r : ℝ) * ((k : ℝ) - 1)
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      = fun G => ∑ i, ∑ j, M G i j ^ 2 := by
    funext G; rfl
  have hterm : ∀ i j : Fin r, Integrable (fun G => M G i j ^ 2) (gaussianMatrix r k) ∧
      ∫ G, M G i j ^ 2 ∂(gaussianMatrix r k)
        = if i = j then 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          else 1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact inverse_wishart_diag_sq_moment hrk i
    · rw [if_neg hij]
      exact inverse_wishart_offdiag_sq_moment hrk i j hij
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hterm _ j).1, fun i j => (hterm i j).2]
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
