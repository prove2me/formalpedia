-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.sum_sgn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:28.413078+00:00
-- url     : https://prove2.me/submissions/1c64dce5-7803-4815-a20b-fb42d8dafd06

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.sum_sgn_eq_zero
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_sgn_not
import Theorems.Thm_BookProof_ChapterScaledDotProduct_flipEquiv_apply_self
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) : ∑ x : (Fin d → Bool), sgn (x i) = 0 := by

  have h : ∑ x : (Fin d → Bool), sgn ((flipEquiv i x) i)
      = ∑ x : (Fin d → Bool), sgn (x i) :=
    Equiv.sum_comp (flipEquiv i) (fun x => sgn (x i))
  have h2 : ∑ x : (Fin d → Bool), sgn ((flipEquiv i x) i)
      = -∑ x : (Fin d → Bool), sgn (x i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      rw [flipEquiv_apply_self, sgn_not]
  linarith [h.symm.trans h2]
