-- Prove2me | solution 1 for BookProof.ChapterH1.resolvent_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:31:10.522502+00:00
-- url     : https://prove2.me/submissions/082683db-6119-4429-b4d6-e1a26bad5761

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : F →L[ℂ] F) (X : F →L[ℂ] F) (γ z : ℂ) (v : F)
    (hTv : T v = z • v) (hz : γ - z ≠ 0)
    (_hXr : (γ • (1 : F →L[ℂ] F) - T) * X = 1)
    (hXl : X * (γ • (1 : F →L[ℂ] F) - T) = 1) :
    X v = (γ - z)⁻¹ • v := by
  have hx := congrArg (fun Y : F →L[ℂ] F => Y v) hXl
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hTv, map_sub, map_smul] at hx
  have hv' : (γ - z) • X v = v := by simpa only [sub_smul] using hx
  calc
    X v = ((γ - z)⁻¹ * (γ - z)) • X v := by rw [inv_mul_cancel₀ hz, one_smul]
    _ = (γ - z)⁻¹ • ((γ - z) • X v) := mul_smul _ _ _
    _ = (γ - z)⁻¹ • v := by rw [hv']
#print axioms solution
