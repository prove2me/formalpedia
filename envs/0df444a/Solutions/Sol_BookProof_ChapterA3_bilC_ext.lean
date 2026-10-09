-- Prove2me | solution 1 for BookProof.ChapterA3.bilC_ext
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:33:57.067529+00:00
-- url     : https://prove2.me/submissions/86929198-8d02-4fec-b6c1-7c964d1499f4

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.bilC_ext
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution {A B : Matrix (Fin 4) (Fin 4) ℂ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ x : Fin 4 → ℂ, bilC A x = bilC B x) : A = B := by

  -- The quadratic form at the indicator of `{i, j}` is `M i i + M i j + M j i + M j j`.
  have expand : ∀ (M : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4),
      bilC M (fun k => if k = i ∨ k = j then 1 else 0)
        = (if i = j then M i i else M i i + M i j + M j i + M j j) := by
    intro M i j
    fin_cases i <;> fin_cases j <;> simp [bilC, Fin.sum_univ_four] <;> ring
  -- Specializing at `i = j` gives the diagonal entries.
  have h_diag (i : Fin 4) : A i i = B i i := by
    have hi := h (fun k => if k = i ∨ k = i then 1 else 0)
    rw [expand, expand] at hi
    simpa using hi
  -- Specializing at `i ≠ j` and using symmetry gives `2 * A i j = 2 * B i j`.
  have h_off_diag (i j : Fin 4) (hij : i ≠ j) : A i j = B i j := by
    have hh := h (fun k => if k = i ∨ k = j then 1 else 0)
    rw [expand, expand] at hh
    simp only [if_neg hij] at hh
    have hAij : A j i = A i j := congr_fun (congr_fun hA i) j
    have hBij : B j i = B i j := congr_fun (congr_fun hB i) j
    rw [hAij, hBij, h_diag i, h_diag j] at hh
    linear_combination hh / 2
  exact Matrix.ext fun i j => if hij : i = j then hij ▸ h_diag i else h_off_diag i j hij
