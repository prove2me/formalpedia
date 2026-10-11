-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:57:13.243352+00:00
-- url     : https://prove2.me/submissions/61abdf0d-be62-4660-b38a-33e9fa953f56

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_hasDerivAt_expApply
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖(NormedSpace.exp (s • A)) x‖ ^ 2)
      (2 * (inner ℂ (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x))).re) t := by

  have hu := hasDerivAt_expApply A x t
  have hinner := hu.inner ℂ hu
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hinner
  have hfun : (fun s : ℝ => (inner ℂ ((NormedSpace.exp (s • A)) x)
      ((NormedSpace.exp (s • A)) x) : ℂ).re)
      = fun s : ℝ => ‖(NormedSpace.exp (s • A)) x‖ ^ 2 := by
    funext s
    simp [← Complex.ofReal_pow]
  have hsym : (inner ℂ (A (NormedSpace.exp (t • A) x)) (NormedSpace.exp (t • A) x) : ℂ).re
      = (inner ℂ (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x)) : ℂ).re := by
    have hc := inner_conj_symm (𝕜 := ℂ) (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x))
    rw [← hc, Complex.conj_re]
  have hval : (Complex.reCLM ((inner ℂ (NormedSpace.exp (t • A) x)
        (A (NormedSpace.exp (t • A) x)) : ℂ)
      + (inner ℂ (A (NormedSpace.exp (t • A) x)) (NormedSpace.exp (t • A) x) : ℂ)))
      = 2 * (inner ℂ (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) x)) : ℂ).re := by
    simp only [Complex.reCLM_apply, Complex.add_re, hsym]
    ring
  rw [← hfun]
  convert hre using 1 <;> (first | rfl | simp [hval, Function.comp])
