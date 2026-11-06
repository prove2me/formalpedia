-- Prove2me | solution 1 for BianchiIX.sech_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:35:27.833444+00:00
-- url     : https://prove2.me/submissions/9ff946c5-768c-4c8e-8f39-fff9db6bcad7

import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

theorem solution {a b : ℝ} (hab : a ≤ b) :
    1 / Real.cosh b ≤ (1 / Real.cosh a) * Real.exp (b - a) := by
  have hd (z : ℝ) : HasDerivAt (fun u => 1 / Real.cosh u)
      (-Real.sinh z / Real.cosh z ^ 2) z := by
    convert! (Real.hasDerivAt_cosh z).inv (ne_of_gt (Real.cosh_pos z)) using 1
    ext u
    simp
  have hbound (z : ℝ) : -Real.sinh z / Real.cosh z ^ 2 ≤ 1 / Real.cosh z := by
    have H : -Real.sinh z ≤ Real.cosh z := by
      simpa only [Real.sinh_neg, Real.cosh_neg] using (Real.sinh_lt_cosh (x := -z)).le
    apply (div_le_iff₀ (sq_pos_of_pos (Real.cosh_pos z))).mpr
    convert! H using 1
    field_simp
  simpa only [one_mul] using le_exp_of_linear_deriv_le (I := univ) convex_univ
    (c := 1) (fun z _ => hd z) (fun z _ => by simpa only [one_mul] using hbound z)
    (mem_univ a) (mem_univ b) hab
