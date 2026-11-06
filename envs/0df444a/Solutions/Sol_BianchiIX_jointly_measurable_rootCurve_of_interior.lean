-- Prove2me | solution 1 for BianchiIX.jointly_measurable_rootCurve_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:45:34.288166+00:00
-- url     : https://prove2.me/submissions/c8ae1cd0-cf7c-4496-84bd-487ebe3e588f

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Theorems.Thm_BianchiIX_measurable_rootCurve_of_interior
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

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


theorem solution {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun p : X × ℝ => rootCurveExtension (l p.1) (r p.1) (f p.1) (df p.1) p.2) ∧
      Measurable (fun p : X × ℝ => rootCurveDerivative (l p.1) (r p.1) (f p.1) (df p.1) p.2) := by
  exact measurable_rootCurve_of_interior (hl.comp measurable_fst) (hr.comp measurable_fst)
    measurable_snd (fun p => hlr p.1)
    (hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun p y hy => hf p.1 y hy)
