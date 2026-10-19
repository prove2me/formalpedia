-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_iteratedDeriv_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:47.014575+00:00
-- url     : https://prove2.me/submissions/4f5c45bb-7b6f-4c0f-8e91-2b3f0ed4101f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology


theorem solution
    (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n upperImaginaryExp x‖ = 1 := by
  have hd : ∀ (c : ℂ) (x : ℝ), HasDerivAt (fun y : ℝ => c * upperImaginaryExp y) (c * (upperImaginaryExp x * Complex.I)) x := by
    intro c x
    unfold upperImaginaryExp
    have h1 : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) Complex.I x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I
    exact h1.cexp.const_mul c
  have h : ∀ n : ℕ, iteratedDeriv n upperImaginaryExp = fun x => Complex.I ^ n * upperImaginaryExp x := by
    intro n
    induction n with
    | zero => funext x; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [(hd _ x).deriv]
      ring
  rw [h n]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  unfold upperImaginaryExp
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

