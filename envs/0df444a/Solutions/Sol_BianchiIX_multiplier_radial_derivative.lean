-- Prove2me | solution 1 for BianchiIX.multiplier_radial_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:03:42.476768+00:00
-- url     : https://prove2.me/submissions/89fe8ad6-8c6e-47df-bf3b-65e65a86beb3

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology


/-- A positive multiplier gives amplitude-preserving ordinary derivatives, including zero amplitude. -/
theorem solution {u m f : ℝ → ℝ} {x a b : ℝ}
    (hu : DifferentiableAt ℝ u x) (hm : DifferentiableAt ℝ m x)
    (hu0 : 0 ≤ u x) (hm0 : 0 < m x)
    (heq : f =ᶠ[𝓝 x] fun y => u y * m y)
    (hdu : |deriv u x| ≤ a * u x)
    (hdl : |deriv (fun y => Real.log (m y)) x| ≤ b) :
    DifferentiableAt ℝ f x ∧ 0 ≤ f x ∧
      deriv f x = m x * (deriv u x + u x * deriv (fun y => Real.log (m y)) x) ∧
      |deriv f x| ≤ f x * (a + b) ∧
      (u x = 0 → f x = 0 ∧ deriv f x = 0) := by
  have Hlog := hm.hasDerivAt.log hm0.ne'
  have Hf := (hu.hasDerivAt.mul hm.hasDerivAt).congr_of_eventuallyEq heq
  have hvalue : f x = u x * m x := heq.self_of_nhds
  have hd : deriv f x = m x * (deriv u x + u x * deriv (fun y => Real.log (m y)) x) := by
    rw [Hf.deriv, Hlog.deriv]
    field_simp
  have H : |deriv f x| ≤ f x * (a + b) := by
    rw [hd, abs_mul, abs_of_pos hm0, hvalue]
    calc
      _ ≤ m x * (|deriv u x| + |u x * deriv (fun y => Real.log (m y)) x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hm0.le
      _ ≤ m x * (a * u x + u x * b) := by
        rw [abs_mul, abs_of_nonneg hu0]
        exact mul_le_mul_of_nonneg_left (add_le_add hdu (mul_le_mul_of_nonneg_left hdl hu0)) hm0.le
      _ = _ := by ring
  refine ⟨Hf.differentiableAt, hvalue ▸ mul_nonneg hu0 hm0.le, hd, H, ?_⟩
  intro hz
  have hzero : f x = 0 := by rw [hvalue, hz, zero_mul]
  exact ⟨hzero, abs_nonpos_iff.mp (by simpa only [hzero, zero_mul] using H)⟩
