-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.flow_mem_of_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:49:56.546253+00:00
-- url     : https://prove2.me/submissions/aeeb7ed9-5280-494e-9c63-02108e6da9ca

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.flow_mem_of_proj
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution {P B : H →L[ℂ] H} (hPB : P * B = B)
    (t : ℝ) {x : H} (hx : P x = x) : P (flow B t x) = flow B t x := by

  set Z : H →L[ℂ] H := (-Complex.I) • B with hZ
  have hPZ : P * Z = Z := by rw [hZ, mul_smul_comm, hPB]
  set f : ℝ → H := fun u => (exp (u • Z)) x with hf
  have hfderiv : ∀ u : ℝ, HasDerivAt f (Z (f u)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => exp (v • Z)) (exp (u • Z) * Z) u :=
      hasDerivAt_exp_smul_const Z u
    have hev : HasFDerivAt (fun S : H →L[ℂ] H => S x)
        ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ) (exp (u • Z)) :=
      ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt
    have h2 := hev.comp_hasDerivAt u h1
    have hcomm : exp (u • Z) * Z = Z * exp (u • Z) := ((Commute.refl Z).smul_left u).exp_left.eq
    simpa [hf, Function.comp_def, hcomm, ContinuousLinearMap.mul_apply] using h2
  set d : ℝ → H := fun u => P (f u) - f u with hd
  have hPfderiv : ∀ u : ℝ, HasDerivAt (fun v => P (f v)) (Z (f u)) u := by
    intro u
    have h := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt u (hfderiv u)
    have hPZ' : P (Z (f u)) = Z (f u) := by
      have := congrArg (fun S : H →L[ℂ] H => S (f u)) hPZ
      simpa [ContinuousLinearMap.mul_apply] using this
    simpa [Function.comp_def, hPZ'] using h
  have hdderiv : ∀ u : ℝ, HasDerivAt d 0 u := by
    intro u
    rw [hd]
    have h := (hPfderiv u).sub (hfderiv u)
    rw [sub_self] at h
    exact h
  have hconst : d t = d 0 :=
    is_const_of_deriv_eq_zero (fun u => (hdderiv u).differentiableAt)
      (fun u => (hdderiv u).deriv) t 0
  have h0 : d 0 = 0 := by simp [hd, hf, hx]
  have hzero : d t = 0 := by rw [hconst, h0]
  have := sub_eq_zero.mp hzero
  simpa [hd, hf, flow, hZ] using this
