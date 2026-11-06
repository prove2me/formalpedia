-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_pair_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:49:29.843159+00:00
-- url     : https://prove2.me/submissions/a459a27b-0fe5-43db-b143-a1ad21a80f0c

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_left
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
import Theorems.Thm_BianchiIX_rootCurveExtension_right
import Theorems.Thm_BianchiIX_rootExtension_pair_bound
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


theorem solution {l r θ B : ℝ} (hlr : l ≤ r) {f g df dg : ℝ → ℝ}
    (hf : ∀ x ∈ Icc l r, 0 < f x) (hg : ∀ x ∈ Icc l r, 0 < g x)
    (hdf : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hdg : ∀ x ∈ Icc l r, |dg x| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, f x ^ 2 + g x ^ 2 ≤ B) (x : ℝ) :
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ (1 + θ / 4) ^ 2 * B := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).1, (rootCurveExtension_left g dg hlr hxl.le).1]
    exact rootExtension_pair_bound (hf l ⟨le_rfl, hlr⟩) (hg l ⟨le_rfl, hlr⟩)
      (by norm_num) (by linarith) (hdf l ⟨le_rfl, hlr⟩) (hdg l ⟨le_rfl, hlr⟩) hθ (hB l ⟨le_rfl, hlr⟩)
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).1, (rootCurveExtension_right g dg hlr hrx.le).1]
    exact rootExtension_pair_bound (hf r ⟨hlr, le_rfl⟩) (hg r ⟨hlr, le_rfl⟩)
      (by norm_num) (by linarith) (hdf r ⟨hlr, le_rfl⟩) (hdg r ⟨hlr, le_rfl⟩) hθ (hB r ⟨hlr, le_rfl⟩)
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).1, (rootCurveExtension_middle g dg hx).1]
  have h := hB x hx
  have hB0 : 0 ≤ B := (add_nonneg (sq_nonneg (f x)) (sq_nonneg (g x))).trans h
  have hθ0 : 0 ≤ θ := by linarith [hdf x hx, abs_nonneg (df x)]
  have hfactor : 1 ≤ (1 + θ / 4) ^ 2 := by nlinarith
  exact h.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hB0])
