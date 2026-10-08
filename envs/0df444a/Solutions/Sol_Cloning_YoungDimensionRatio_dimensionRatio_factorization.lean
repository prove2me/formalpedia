-- Prove2me | solution 1 for Cloning.YoungDimensionRatio.dimensionRatio_factorization
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:50:37.535407+00:00
-- url     : https://prove2.me/submissions/2d38119f-c02d-4498-9935-a2052e79d524

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

theorem crossingGap_pos {r k : ℕ} (a : Fin r × Fin k) : 0 < crossingGap a := by
  have hi : (a.1.val : ℝ) < r := by exact_mod_cast a.1.isLt
  have hj : 0 ≤ (a.2.val : ℝ) := Nat.cast_nonneg _
  dsimp [crossingGap]
  linarith

end Cloning.YoungDimensionRatio

open Cloning.YoungDimensionRatio in
/-- An exact rescaling identity, before taking any limit. -/
theorem solution (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) :
    dimensionRatio r k row = leadingConstant r k * N ^ (r * k) *
      ∏ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N) := by
  have hfactor (a : Fin r × Fin k) :
      (row a.1 + crossingGap a) / crossingGap a =
        ((1 / ((r : ℝ) * crossingGap a)) * N) *
          ((r : ℝ) * (row a.1 + crossingGap a) / N) := by
    have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
    have hg : crossingGap a ≠ 0 := (crossingGap_pos a).ne'
    field_simp
  unfold dimensionRatio
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [leadingConstant, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
