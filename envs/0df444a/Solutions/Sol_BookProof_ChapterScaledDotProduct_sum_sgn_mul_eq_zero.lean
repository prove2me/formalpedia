-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:43.134853+00:00
-- url     : https://prove2.me/submissions/9358710b-8de1-4dee-bbf2-c6c79ab67a9c

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.sum_sgn_mul_eq_zero
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_sgn_not
import Theorems.Thm_BookProof_ChapterScaledDotProduct_flipEquiv_apply_self
import Theorems.Thm_BookProof_ChapterScaledDotProduct_flipEquiv_apply_of_ne
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {i j : Fin d} (hij : i ≠ j) :
    ∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) = 0 := by

  have h : ∑ x : (Fin d → Bool), sgn ((flipEquiv i x) i) * sgn ((flipEquiv i x) j)
      = ∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) :=
    Equiv.sum_comp (flipEquiv i) (fun x => sgn (x i) * sgn (x j))
  have h2 : ∑ x : (Fin d → Bool), sgn ((flipEquiv i x) i) * sgn ((flipEquiv i x) j)
      = -∑ x : (Fin d → Bool), sgn (x i) * sgn (x j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [flipEquiv_apply_self, flipEquiv_apply_of_ne (Ne.symm hij), sgn_not]
    ring
  linarith [h.symm.trans h2]
