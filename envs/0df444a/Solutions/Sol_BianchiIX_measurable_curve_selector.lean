-- Prove2me | solution 1 for BianchiIX.measurable_curve_selector
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:37:56.988054+00:00
-- url     : https://prove2.me/submissions/c341e57f-b800-412d-9c03-6c06f34305d4

import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Theorems.Thm_BianchiIX_curveSampleStep_samples
import Theorems.Thm_BianchiIX_measurable_curveSampleStep
import Theorems.Thm_BianchiIX_tendsto_adjacent_secant
import Theorems.Thm_BianchiIX_tendsto_curveSampleStep
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


/-- Interior Borel values determine measurable values and derivatives at every
measurable selector of the closed interval. No endpoint measurability is assumed. -/
theorem solution {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hlr : ∀ q, l q < r q) (hxi : ∀ q, x q ∈ Icc (l q) (r q))
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun q => f q (x q)) ∧ Measurable (fun q => df q (x q)) := by
  let h : X → ℕ → ℝ := fun q => curveSampleStep (l q) (r q) (x q)
  have hsample q n := curveSampleStep_samples (hlr q) (hxi q) n
  have hm₁ (n : ℕ) : Measurable (fun q => f q (x q + h q n)) := by
    have H := hm.comp (measurable_id.prodMk (hx.add (measurable_curveSampleStep hl hr hx n)))
    convert! H using 1
    ext q
    exact (if_pos (hsample q n).2.1).symm
  have hm₂ (n : ℕ) : Measurable (fun q => f q (x q + 2 * h q n)) := by
    have H := hm.comp (measurable_id.prodMk
      (hx.add ((measurable_curveSampleStep hl hr hx n).const_mul 2)))
    convert! H using 1
    ext q
    exact (if_pos (hsample q n).2.2).symm
  constructor
  · apply measurable_of_tendsto_metrizable hm₁
    apply tendsto_pi_nhds.mpr
    intro q
    apply (hf q (x q) (hxi q)).continuousWithinAt.tendsto.comp
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using tendsto_const_nhds.add (tendsto_curveSampleStep (l q) (r q) (x q))
    · exact ⟨(hsample q n).2.1.1.le, (hsample q n).2.1.2.le⟩
  · apply measurable_of_tendsto_metrizable
      (fun n => ((hm₂ n).sub (hm₁ n)).div (measurable_curveSampleStep hl hr hx n))
    apply tendsto_pi_nhds.mpr
    intro q
    exact tendsto_adjacent_secant (hf q (x q) (hxi q))
      (tendsto_curveSampleStep (l q) (r q) (x q))
      (fun n => (hsample q n).1)
      (fun n => ⟨(hsample q n).2.1.1.le, (hsample q n).2.1.2.le⟩)
      (fun n => ⟨(hsample q n).2.2.1.le, (hsample q n).2.2.2.le⟩)
