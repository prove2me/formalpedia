-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.hasDerivAt_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:48.018691+00:00
-- url     : https://prove2.me/submissions/007c832e-6c96-40ae-8fce-985cf760207f

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.hasDerivAt_flow
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (B : H →L[ℂ] H) (x : H) (u : ℝ) :
    HasDerivAt (fun v : ℝ => flow B v x) ((-Complex.I) • B (flow B u x)) u := by

  set Z : H →L[ℂ] H := (-Complex.I) • B with hZ
  have h1 : HasDerivAt (fun v : ℝ => exp (v • Z)) (exp (u • Z) * Z) u :=
    hasDerivAt_exp_smul_const Z u
  have hev : HasFDerivAt (fun S : H →L[ℂ] H => S x)
      ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ) (exp (u • Z)) :=
    ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt
  have h2 := hev.comp_hasDerivAt u h1
  have hcomm : exp (u • Z) * Z = Z * exp (u • Z) := ((Commute.refl Z).smul_left u).exp_left.eq
  rw [hcomm] at h2
  have h3 : HasDerivAt (fun v : ℝ => (exp (v • Z)) x) ((Z * exp (u • Z)) x) u := by
    simpa [Function.comp_def] using h2
  exact h3
