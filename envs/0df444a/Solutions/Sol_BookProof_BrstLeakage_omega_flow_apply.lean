-- Prove2me | solution 1 for BookProof.BrstLeakage.omega_flow_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:28.153563+00:00
-- url     : https://prove2.me/submissions/94114673-09e6-4f10-9fd1-ef4af1508c30

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.omega_flow_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) (x : E) :
    Om (flow A t x) = flow A t (Om x) := by

  have hc : Commute (t • ((-Complex.I) • A)) Om := (h.smul_left (-Complex.I)).smul_left t
  have : exp (t • ((-Complex.I) • A)) * Om = Om * exp (t • ((-Complex.I) • A)) :=
    (hc.exp_left).eq
  have := congrArg (fun T : E →L[ℂ] E => T x) this.symm
  simpa [flow, ContinuousLinearMap.mul_apply] using this
