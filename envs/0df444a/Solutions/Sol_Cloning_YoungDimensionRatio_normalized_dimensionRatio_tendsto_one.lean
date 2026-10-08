-- Prove2me | solution 1 for Cloning.YoungDimensionRatio.normalized_dimensionRatio_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:53:42.954552+00:00
-- url     : https://prove2.me/submissions/a1555539-4569-497f-90aa-6a944b28f538

import Definitions.Def_Cloning_YoungDimensionRatio
import Theorems.Thm_Cloning_YoungDimensionRatio_dimensionRatio_relative_error
import Theorems.Thm_Cloning_YoungDimensionRatio_error_envelope_tendsto_zero
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
/-- Leading-order normalization for the concrete Weyl ratio, derived
from row proximity and the proved quantitative estimate. -/
theorem solution (r k : ℕ) (hr : 0 < r)
    (row : ℕ → Fin r → ℝ) (N δ : ℕ → ℝ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ n i, |row n i / N n - 1 / (r : ℝ)| ≤ δ n) :
    Tendsto (fun n => dimensionRatio r k (row n) /
      (leadingConstant r k * (N n) ^ (r * k))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun n => dimensionRatio r k (row n) /
      (leadingConstant r k * (N n) ^ (r * k)) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => by simpa only [Real.norm_eq_abs] using
        dimensionRatio_relative_error r k (row n) (N n) (δ n) hr (hNpos n) (hclose n))
    exact error_envelope_tendsto_zero r k N δ hN hδ
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1
