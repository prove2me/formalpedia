-- Prove2me | solution 1 for BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:13:40.559109+00:00
-- url     : https://prove2.me/submissions/60e1b9c9-b747-4533-a4a3-e6899b46b8f6

-- Generated from ChapterUniformPrior.lean — solution of BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
import Mathlib
import Definitions.Def_ChapterUniformPrior
import Theorems.Thm_BookProof_ChapterUniformPrior_isRelabelingInvariant_iff_constant
open BookProof.ChapterUniformPrior



open scoped BigOperators


variable {Hyp Data : Type*}

variable {Hyp Data : Type*}

set_option maxHeartbeats 1000000 in
theorem solution [Fintype Hyp] [Nonempty Hyp]
    (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (hsum : ∑ x, p x = 1) :
    p = fun _ => (1 : ℝ) / Fintype.card Hyp := by

  obtain ⟨c, hc⟩ := isRelabelingInvariant_iff_constant p |>.1 hp;
  simp_all only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, funext_iff, one_div,
      forall_const];
  exact eq_inv_of_mul_eq_one_right hsum
