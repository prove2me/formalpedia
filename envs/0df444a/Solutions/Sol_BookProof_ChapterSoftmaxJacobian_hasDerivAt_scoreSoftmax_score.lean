-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:03:11.62956+00:00
-- url     : https://prove2.me/submissions/121a513b-9cd7-49d5-926d-7ce83d4ae44b

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

theorem sm_hasDerivAt {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta
        (BookProof.ChapterSoftmaxJacobian.scorePerturb s i t) j)
      (BookProof.ChapterSoftmaxJacobian.softmaxJacobian beta s i j) 0 := by
  classical
  have hl : ∀ l, HasDerivAt (fun t => Real.exp (beta * BookProof.ChapterSoftmaxJacobian.scorePerturb s i t l))
      (Real.exp (beta * s l) * (beta * if l = i then 1 else 0)) 0 := by
    intro l
    have h1 : HasDerivAt (fun t => beta * BookProof.ChapterSoftmaxJacobian.scorePerturb s i t l)
        (beta * if l = i then 1 else 0) 0 := by
      unfold BookProof.ChapterSoftmaxJacobian.scorePerturb
      by_cases hli : l = i
      · simp only [hli, if_true]
        exact ((hasDerivAt_id (0:ℝ)).const_add (s i)).const_mul beta
      · simp only [hli, if_false, add_zero, mul_zero]
        exact hasDerivAt_const _ _
    have h2 := h1.exp
    convert h2 using 2
    simp [BookProof.ChapterSoftmaxJacobian.scorePerturb]
  have hD : HasDerivAt (fun t => ∑ l, Real.exp (beta * BookProof.ChapterSoftmaxJacobian.scorePerturb s i t l))
      (∑ l, Real.exp (beta * s l) * (beta * if l = i then 1 else 0)) 0 :=
    HasDerivAt.fun_sum (fun l _ => hl l)
  have hD0 : (∑ l, Real.exp (beta * BookProof.ChapterSoftmaxJacobian.scorePerturb s i 0 l)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hq := (hl j).div hD hD0
  have hsum : (∑ l, Real.exp (beta * s l) * (beta * if l = i then 1 else 0)) = Real.exp (beta * s i) * beta := by
    simp [mul_ite, mul_zero, Finset.sum_ite_eq']
  simp only [BookProof.ChapterSoftmaxJacobian.scorePerturb_zero, hsum] at hq hD0
  refine hq.congr_deriv ?_
  unfold BookProof.ChapterSoftmaxJacobian.softmaxJacobian BookProof.ChapterSoftmaxSharpness.scoreSoftmax
  field_simp
  try (split_ifs <;> ring)

variable {m : ℕ}
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j)
      (softmaxJacobian beta s i j) 0 := by
  exact sm_hasDerivAt beta s i j
