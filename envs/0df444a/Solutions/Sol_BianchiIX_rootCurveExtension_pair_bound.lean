-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:50:27.850009+00:00
-- url     : https://prove2.me/submissions/6f166e05-0fc5-4e26-8e2d-72d7bdd4951b

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_pair_bound_sharp
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
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ (25 / 16) * B := by
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr⟩
  have hB0 : 0 ≤ B := (add_nonneg (sq_nonneg (f l)) (sq_nonneg (g l))).trans (hB l hl)
  have hθ0 : 0 ≤ θ := by linarith [hdf l hl, abs_nonneg (df l)]
  have hfactor : (1 + θ / 4) ^ 2 ≤ (25 / 16 : ℝ) := by nlinarith
  exact (rootCurveExtension_pair_bound_sharp hlr hf hg hdf hdg hθ hB x).trans
    (mul_le_mul_of_nonneg_right hfactor hB0)
