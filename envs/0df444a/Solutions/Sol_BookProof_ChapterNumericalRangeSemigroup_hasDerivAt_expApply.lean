-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:59.17672+00:00
-- url     : https://prove2.me/submissions/761cc512-b003-408f-9c69-6ebbcb96caab

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)) x) (A (NormedSpace.exp (t • A) x)) t := by

  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A))
      (NormedSpace.exp (t • A) * A) t := hasDerivAt_exp_smul_const A t
  set Φ : (E →L[ℂ] E) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ with hΦ
  have h2 := Φ.hasFDerivAt.comp_hasDerivAt t h1
  have hcomm : NormedSpace.exp (t • A) * A = A * NormedSpace.exp (t • A) := by
    have hc : Commute (t • A) A := (Commute.refl A).smul_left t
    exact hc.exp_left.eq
  convert h2 using 1 <;> (first | rfl | simp [hΦ, hcomm, Function.comp])
