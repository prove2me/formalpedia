-- Prove2me | solution 1 for BianchiIX.jointly_measurable_amplitudeCurve
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:47:59.094198+00:00
-- url     : https://prove2.me/submissions/177b41b8-0dd4-4b42-bbca-9fb293a9cc96

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_hasDerivAt_amplitudeCurveExtension
import Theorems.Thm_BianchiIX_hasDerivWithinAt_amplitudeRoot
import Theorems.Thm_BianchiIX_jointly_measurable_rootCurve_of_interior
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX
open Set


theorem solution {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {U dU : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hpos : ∀ q x, x ∈ Icc (l q) (r q) → 0 < U q x)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then U p.1 p.2 else 0))
    (hU : ∀ q x, x ∈ Icc (l q) (r q) →
      HasDerivWithinAt (U q) (dU q x) (Icc (l q) (r q)) x) :
    Measurable (fun p : X × ℝ => amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1) p.2) ∧
      Measurable (fun p : X × ℝ => deriv (amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1)) p.2) := by
  have hmroot : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then Real.sqrt (U p.1 p.2) else 0) := by
    convert! Real.continuous_sqrt.measurable.comp hm using 1
    ext p
    by_cases hp : l p.1 < p.2 ∧ p.2 < r p.1 <;> simp [hp]
  obtain ⟨hs, hds⟩ := jointly_measurable_rootCurve_of_interior hl hr hlr hmroot
    (fun q x hx => hasDerivWithinAt_amplitudeRoot (hpos q x hx) (hU q x hx))
  refine ⟨hs.pow_const 2, ?_⟩
  have H := (hs.const_mul 2).mul hds
  convert! H using 1
  ext p
  exact (hasDerivAt_amplitudeCurveExtension (hlr p.1) (hpos p.1) (hU p.1) p.2).deriv
