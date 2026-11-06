-- Prove2me | solution 1 for BianchiIX.continuous_rootCurveDerivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:40:24.119616+00:00
-- url     : https://prove2.me/submissions/d086d4aa-864a-4b74-81d4-765ea1a5a963

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_continuous_rootCutoff
import Theorems.Thm_BianchiIX_rootCurveExtension_left
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
import Theorems.Thm_BianchiIX_rootCurveExtension_right
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {l r : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hdf : ContinuousOn df (Icc l r)) : Continuous (rootCurveDerivative l r f df) := by
  have hL : ContinuousOn (rootCurveDerivative l r f df) (Iic l) := by
    have hc : Continuous (fun x => df l * rootCutoff (-(x - l) / f l)) :=
      (continuous_rootCutoff.comp ((continuous_id.sub continuous_const).neg.div_const (f l))).const_mul (df l)
    exact hc.continuousOn.congr (fun x hx => (rootCurveExtension_left f df hlr hx).2)
  have hM : ContinuousOn (rootCurveDerivative l r f df) (Icc l r) :=
    hdf.congr (fun x hx => (rootCurveExtension_middle f df hx).2)
  have hR : ContinuousOn (rootCurveDerivative l r f df) (Ici r) := by
    have hc : Continuous (fun x => df r * rootCutoff ((x - r) / f r)) :=
      (continuous_rootCutoff.comp ((continuous_id.sub continuous_const).div_const (f r))).const_mul (df r)
    exact hc.continuousOn.congr (fun x hx => (rootCurveExtension_right f df hlr hx).2)
  have h := (hL.union_of_isClosed hM isClosed_Iic isClosed_Icc).union_of_isClosed hR
    (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  have hu : (Iic l ∪ Icc l r) ∪ Ici r = univ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ici, mem_univ, iff_true]
    rcases le_total x l with hx | hx
    · exact Or.inl (Or.inl hx)
    rcases le_total x r with hr | hr
    · exact Or.inl (Or.inr ⟨hx, hr⟩)
    · exact Or.inr hr
  rwa [hu, continuousOn_univ] at h
