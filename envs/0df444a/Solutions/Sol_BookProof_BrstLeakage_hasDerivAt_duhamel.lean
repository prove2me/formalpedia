-- Prove2me | solution 1 for BookProof.BrstLeakage.hasDerivAt_duhamel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:48:52.506001+00:00
-- url     : https://prove2.me/submissions/7b07e522-54e0-4646-9842-786e9dc38b48

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.hasDerivAt_duhamel
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (X Y : E →L[ℂ] E) (t s : ℝ) (x : E) :
    HasDerivAt (fun u : ℝ => (exp ((t - u) • X)) ((exp (u • Y)) x))
      ((exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))) s := by

  have hc : HasDerivAt (fun u : ℝ => exp ((t - u) • X)) (-(exp ((t - s) • X) * X)) s := by
    have h1 : HasDerivAt (fun u : ℝ => exp (u • X)) (exp ((t - s) • X) * X) (t - s) :=
      hasDerivAt_exp_smul_const X (t - s)
    have h2 : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    simpa [Function.comp_def] using h1.scomp s h2
  have hd : HasDerivAt (fun u : ℝ => exp (u • Y)) (exp (s • Y) * Y) s :=
    hasDerivAt_exp_smul_const Y s
  have hmul := hc.mul hd
  have hev : HasFDerivAt (fun T : E →L[ℂ] E => T x)
      ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ) (exp ((t - s) • X) * exp (s • Y)) :=
    ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt
  have hres := hev.comp_hasDerivAt s hmul
  have hcomm : exp (s • Y) * Y = Y * exp (s • Y) := ((Commute.refl Y).smul_left s).exp_left.eq
  have heq : (-(exp ((t - s) • X) * X) * exp (s • Y) + exp ((t - s) • X) * (exp (s • Y) * Y)) x
      = (exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x)) := by
    rw [hcomm]
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
    abel
  rw [← heq]
  exact hres
