-- Prove2me | solution 1 for BookProof.BrstLeakage.flow_truncGen_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:14.342228+00:00
-- url     : https://prove2.me/submissions/6dabf9ca-ac53-48c0-a8fd-e063036ba0b9

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.flow_truncGen_mem
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {P H : E →L[ℂ] E} (hP : IsIdempotentElem P) (t : ℝ) {x : E}
    (hx : P x = x) : P (flow (truncGen P H) t x) = flow (truncGen P H) t x := by

  set Z : E →L[ℂ] E := (-Complex.I) • truncGen P H with hZ
  have hPZ : P * Z = Z := by
    rw [hZ, truncGen]
    rw [mul_smul_comm, ← mul_assoc, ← mul_assoc, hP.eq]
  set f : ℝ → E := fun u => (exp (u • Z)) x with hf
  set d : ℝ → E := fun u => P (f u) - f u with hd
  have hfderiv : ∀ u : ℝ, HasDerivAt f (Z (f u)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => exp (v • Z)) (exp (u • Z) * Z) u :=
      hasDerivAt_exp_smul_const Z u
    have hev : HasFDerivAt (fun T : E →L[ℂ] E => T x)
        ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ) (exp (u • Z)) :=
      ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt
    have h2 := hev.comp_hasDerivAt u h1
    have hcomm : exp (u • Z) * Z = Z * exp (u • Z) := ((Commute.refl Z).smul_left u).exp_left.eq
    simpa [hf, Function.comp_def, hcomm, ContinuousLinearMap.mul_apply] using h2
  have hPfderiv : ∀ u : ℝ, HasDerivAt (fun v => P (f v)) (Z (f u)) u := by
    intro u
    have := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt u (hfderiv u)
    have hPZ' : P (Z (f u)) = Z (f u) := by
      have := congrArg (fun T : E →L[ℂ] E => T (f u)) hPZ
      simpa [ContinuousLinearMap.mul_apply] using this
    simpa [Function.comp_def, hPZ'] using this
  have hdderiv : ∀ u : ℝ, HasDerivAt d 0 u := by
    intro u
    rw [hd]
    convert (hPfderiv u).sub (hfderiv u) using 1 <;> (first | rfl | simp)
  have hconst : d t = d 0 := by
    have : ∀ u : ℝ, deriv d u = 0 := fun u => (hdderiv u).deriv
    have hdiff : Differentiable ℝ d := fun u => (hdderiv u).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff this t 0
  have h0 : d 0 = 0 := by simp [hd, hf, hx]
  have : d t = 0 := by rw [hconst, h0]
  have := sub_eq_zero.mp this
  simpa [hd, hf, flow, hZ] using this
