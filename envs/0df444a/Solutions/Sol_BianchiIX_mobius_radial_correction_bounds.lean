-- Prove2me | solution 1 for BianchiIX.mobius_radial_correction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:02:42.041676+00:00
-- url     : https://prove2.me/submissions/7e6ff81b-06f8-4d82-b705-573b0cb24484

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The Mobius step differs from the identity by a quadratic value and a linear radial derivative. -/
theorem solution {f : ℝ → ℝ} {x r K D : ℝ}
    (hf : DifferentiableAt ℝ f x) (hr : 0 ≤ r) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hx : 0 ≤ f x ∧ f x ≤ 1 / 2) (hxr : f x ≤ K * r) (hd : |deriv f x| ≤ D) :
    let E := fun a => f a / (1 - f a) - f a
    DifferentiableAt ℝ E x ∧ |E x| ≤ 2 * K ^ 2 * r ^ 2 ∧ |deriv E x| ≤ 8 * K * D * r := by
  intro E
  have ht : 0 < 1 - f x := by linarith only [hx.2]
  have hne := ht.ne'
  have hden : 1 / (1 - f x) ≤ 2 := (div_le_iff₀ ht).mpr (by linarith only [hx.2])
  have hden2 : 1 / (1 - f x) ^ 2 ≤ 4 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (1 - f x)) hden 2
    simpa only [div_pow, one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using H
  have HE : HasDerivAt E (f x * (2 - f x) * deriv f x / (1 - f x) ^ 2) x := by
    convert! (hf.hasDerivAt.div (hf.hasDerivAt.const_sub 1) hne).sub hf.hasDerivAt using 1
    field_simp
    ring
  have hx0 := hx.1
  have htwo : 0 ≤ 2 - f x := by linarith only [hx.2]
  refine ⟨HE.differentiableAt, ?_, ?_⟩
  · have heq : E x = (f x) ^ 2 / (1 - f x) := by dsimp only [E]; field_simp; ring
    rw [heq, abs_of_nonneg (by positivity : 0 ≤ (f x) ^ 2 / (1 - f x))]
    calc
      _ = (f x) ^ 2 * (1 / (1 - f x)) := by ring
      _ ≤ (K * r) ^ 2 * 2 := by gcongr
      _ = _ := by ring
  · rw [HE.deriv, abs_div, abs_mul, abs_mul, abs_of_nonneg hx.1,
      abs_of_nonneg htwo, abs_of_nonneg (sq_nonneg (1 - f x))]
    calc
      _ = f x * (2 - f x) * |deriv f x| * (1 / (1 - f x) ^ 2) := by ring
      _ ≤ (K * r) * 2 * D * 4 := by gcongr; linarith only [hx.1]
      _ = _ := by ring
