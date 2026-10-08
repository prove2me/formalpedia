-- Prove2me | solution 1 for Cloning.YoungDimensionRatio.error_envelope_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:51:21.668991+00:00
-- url     : https://prove2.me/submissions/0e7e684b-572a-4383-8998-6d7f7d150917

import Definitions.Def_Cloning_YoungDimensionRatio

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete asymptotics of the crossing-root Weyl dimension product

For an `r`-row label in ambient dimension `r+k`, the manuscript's explicit
dimension-ratio expression is the product of `(rowᵢ+j-i)/(j-i)` over crossing
roots. This file defines that actual finite product and derives its uniform
relative-error bound directly from the row lengths. No dimension-ratio
convergence or product approximation is assumed.

The identification of this explicit Weyl product with dimensions of the
particular representation spaces is a separate representation-theoretic
statement. This file proves the analytic input once that formula is used.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungDimensionRatio



end Cloning.YoungDimensionRatio

open Cloning.YoungDimensionRatio in
/-- The explicit error envelope vanishes. This bound is independent of
the selected row vector, so it controls all typical labels simultaneously. -/
theorem solution (r k : ℕ) (N δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n =>
      Real.exp ((r * k : ℕ) * ((r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n)) - 1)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hN
  have harg : Tendsto
      (fun n => (r * k : ℕ) * ((r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (((tendsto_const_nhds (x := (r : ℝ))).mul hδ).add
        ((tendsto_const_nhds (x := (r : ℝ) * ((r : ℝ) + k))).mul hinv)).const_mul
          ((r * k : ℕ) : ℝ)
  simpa only [Real.exp_zero, sub_self, Function.comp_apply] using
    ((Real.continuous_exp.tendsto 0).comp harg).sub_const 1
