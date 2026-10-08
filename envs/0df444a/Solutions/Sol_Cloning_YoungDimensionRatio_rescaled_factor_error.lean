-- Prove2me | solution 1 for Cloning.YoungDimensionRatio.rescaled_factor_error
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:51:59.734421+00:00
-- url     : https://prove2.me/submissions/17469cab-9b3c-475e-9275-56befbf42cbc

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

theorem crossingGap_le {r k : ℕ} (a : Fin r × Fin k) :
    crossingGap a ≤ (r : ℝ) + k := by
  have hj : (a.2.val : ℝ) < k := by exact_mod_cast a.2.isLt
  have hi : 0 ≤ (a.1.val : ℝ) := Nat.cast_nonneg _
  dsimp [crossingGap]
  linarith

end Cloning.YoungDimensionRatio

open Cloning.YoungDimensionRatio in
/-- The per-root rescaled factor is uniformly close to one whenever the
row proportions are uniformly close to the flat spectrum. -/
theorem solution (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ) (a : Fin r × Fin k) :
    |(r : ℝ) * (row a.1 + crossingGap a) / N - 1| ≤
      (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N := by
  have hr' : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have heq : (r : ℝ) * (row a.1 + crossingGap a) / N - 1 =
      (r : ℝ) * (row a.1 / N - 1 / (r : ℝ)) + (r : ℝ) * crossingGap a / N := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(r : ℝ) * (row a.1 / N - 1 / (r : ℝ))| +
        |(r : ℝ) * crossingGap a / N| := abs_add_le _ _
    _ = (r : ℝ) * |row a.1 / N - 1 / (r : ℝ)| + (r : ℝ) * crossingGap a / N := by
      rw [abs_mul, abs_of_pos hr', abs_of_nonneg
        (div_nonneg (mul_nonneg hr'.le (crossingGap_pos a).le) hN.le)]
    _ ≤ (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N := by
      apply add_le_add (mul_le_mul_of_nonneg_left (hclose a.1) hr'.le)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (crossingGap_le a) hr'.le) hN.le
