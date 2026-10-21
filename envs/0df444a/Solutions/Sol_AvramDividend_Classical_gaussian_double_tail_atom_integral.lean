-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T23:07:24.406434+00:00
-- url     : https://prove2.me/submissions/694d4f39-1fef-43c0-bd01-facbf7d00242

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Exact single-jump contribution to the Gaussian Volterra double-tail kernel. -/
theorem solution
    (θ z : ℝ) :
    (∫ t in (0 : ℝ)..z,
      θ ^ 2 * ((z - t) * Real.exp (-θ * t))) =
      Real.exp (-θ * z) - 1 + θ * z := by
  let B : ℝ → ℝ := fun t =>
    Real.exp (-θ * t) * (1 + θ * (t - z))
  have hB : ∀ t : ℝ,
      HasDerivAt B (θ ^ 2 * ((z - t) * Real.exp (-θ * t))) t := by
    intro t
    have hlinear : HasDerivAt (fun s : ℝ => -θ * s) (-θ) t := by
      simpa using (hasDerivAt_id t).const_mul (-θ)
    have hexp : HasDerivAt
        (fun s : ℝ => Real.exp (-θ * s))
        (Real.exp (-θ * t) * (-θ)) t :=
      hlinear.exp
    have hlinear2 : HasDerivAt (fun s : ℝ => θ * (s - z)) θ t := by
      have hsub : HasDerivAt (fun s : ℝ => s - z) 1 t := by
        simpa using (hasDerivAt_id t).sub_const z
      simpa using hsub.const_mul θ
    have hsecond : HasDerivAt
        (fun s : ℝ => 1 + θ * (s - z)) θ t := by
      simpa using hlinear2.const_add (1 : ℝ)
    change HasDerivAt
      (fun s : ℝ => Real.exp (-θ * s) * (1 + θ * (s - z)))
      (θ ^ 2 * ((z - t) * Real.exp (-θ * t))) t
    convert hexp.mul hsecond using 1 <;> (first | rfl | ring | simp)
  have hc : Continuous (fun t : ℝ =>
      θ ^ 2 * ((z - t) * Real.exp (-θ * t))) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ => θ ^ 2 * ((z - t) * Real.exp (-θ * t)))
      MeasureTheory.volume (0 : ℝ) z :=
    hc.intervalIntegrable (0 : ℝ) z
  have hFTC :
      (∫ t in (0 : ℝ)..z,
        θ ^ 2 * ((z - t) * Real.exp (-θ * t))) =
        B z - B 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hB t) hint
  convert hFTC using 1 <;> simp [B] <;> ring
