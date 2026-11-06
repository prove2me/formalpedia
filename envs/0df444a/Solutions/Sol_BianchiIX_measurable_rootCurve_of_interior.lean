-- Prove2me | solution 1 for BianchiIX.measurable_rootCurve_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:43:14.905378+00:00
-- url     : https://prove2.me/submissions/993b451a-4152-4a69-a105-2eb5f53498fc

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Theorems.Thm_BianchiIX_continuous_rootCutoff
import Theorems.Thm_BianchiIX_measurable_curve_selector
import Theorems.Thm_BianchiIX_measurable_rootExtension
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


/-- Recover the endpoint data before extending the curve. The arbitrary values
of the original functions outside their intervals play no role. -/
theorem solution {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hlr : ∀ q, l q < r q)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun q => rootCurveExtension (l q) (r q) (f q) (df q) (x q)) ∧
      Measurable (fun q => rootCurveDerivative (l q) (r q) (f q) (df q) (x q)) := by
  classical
  obtain ⟨hfl, hdl⟩ := measurable_curve_selector hl hr hl hlr
    (fun q => ⟨le_rfl, (hlr q).le⟩) hm hf
  obtain ⟨hfr, hdr⟩ := measurable_curve_selector hl hr hr hlr
    (fun q => ⟨(hlr q).le, le_rfl⟩) hm hf
  let z : X → ℝ := fun q => max (l q) (min (x q) (r q))
  have hz : Measurable z := hl.max (hx.min hr)
  have hzi q : z q ∈ Icc (l q) (r q) :=
    ⟨le_max_left _ _, max_le (hlr q).le (min_le_right _ _)⟩
  obtain ⟨hfm, hdm⟩ := measurable_curve_selector hl hr hz hlr hzi hm hf
  have heq q (h₁ : ¬x q < l q) (h₂ : ¬r q < x q) : z q = x q := by
    simp only [z, min_eq_left (le_of_not_gt h₂), max_eq_right (le_of_not_gt h₁)]
  constructor
  · have H : Measurable (fun q =>
        if x q < l q then rootExtension (f q (l q)) (df q (l q)) (-1) (x q - l q)
        else if r q < x q then rootExtension (f q (r q)) (df q (r q)) 1 (x q - r q)
        else f q (z q)) :=
      Measurable.ite (measurableSet_lt hx hl)
        (measurable_rootExtension hfl hdl measurable_const (hx.sub hl))
        (Measurable.ite (measurableSet_lt hr hx)
          (measurable_rootExtension hfr hdr measurable_const (hx.sub hr)) hfm)
    convert! H using 1
    ext q
    unfold rootCurveExtension
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · rw [heq q h₁ h₂]
  · have H : Measurable (fun q =>
        if x q < l q then df q (l q) * rootCutoff (-(x q - l q) / f q (l q))
        else if r q < x q then df q (r q) * rootCutoff ((x q - r q) / f q (r q))
        else df q (z q)) :=
      Measurable.ite (measurableSet_lt hx hl)
        (hdl.mul (continuous_rootCutoff.measurable.comp ((hx.sub hl).neg.div hfl)))
        (Measurable.ite (measurableSet_lt hr hx)
          (hdr.mul (continuous_rootCutoff.measurable.comp ((hx.sub hr).div hfr))) hdm)
    convert! H using 1
    ext q
    unfold rootCurveDerivative
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · rw [heq q h₁ h₂]
