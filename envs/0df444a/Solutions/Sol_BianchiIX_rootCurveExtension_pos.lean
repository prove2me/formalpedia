-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:48:27.369165+00:00
-- url     : https://prove2.me/submissions/bad7f598-13fa-485c-9d56-72fdddc4a45b

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_left
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
import Theorems.Thm_BianchiIX_rootCurveExtension_right
import Theorems.Thm_BianchiIX_rootExtension_pos
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


theorem solution {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (hθ : θ ≤ 1) (x : ℝ) : 0 < rootCurveExtension l r f df x := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).1]
    exact rootExtension_pos (hpos l ⟨le_rfl, hlr⟩) (by norm_num) (by linarith)
      (hd l ⟨le_rfl, hlr⟩) hθ
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).1]
    exact rootExtension_pos (hpos r ⟨hlr, le_rfl⟩) (by norm_num) (by linarith)
      (hd r ⟨hlr, le_rfl⟩) hθ
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).1]
  exact hpos x hx
