-- Prove2me | solution 1 for Cloning.YoungDimensionRatio.dimensionRatio_relative_error
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:52:43.716979+00:00
-- url     : https://prove2.me/submissions/b00b2de2-69f9-4e18-be25-66e711b20590

import Definitions.Def_Cloning_YoungDimensionRatio
import Theorems.Thm_Cloning_YoungDimensionRatio_dimensionRatio_factorization
import Theorems.Thm_Cloning_YoungDimensionRatio_rescaled_factor_error
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

theorem leadingConstant_pos (r k : ℕ) (hr : 0 < r) : 0 < leadingConstant r k := by
  apply Finset.prod_pos
  intro a _
  exact one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr hr) (crossingGap_pos a))

end Cloning.YoungDimensionRatio

open Cloning.YoungDimensionRatio in
/-- A uniform quantitative estimate for the actual Weyl ratio product.
The right-hand side tends to zero whenever `δ → 0` and `N → ∞`.
In particular, this proves uniform leading-order asymptotics on the
manuscript's typical row sets without assuming a product approximation. -/
theorem solution (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ) :
    |dimensionRatio r k row / (leadingConstant r k * N ^ (r * k)) - 1| ≤
      Real.exp ((r * k : ℕ) * ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N)) - 1 := by
  let f : Fin r × Fin k → ℝ := fun a => (r : ℝ) * (row a.1 + crossingGap a) / N
  have hden : leadingConstant r k * N ^ (r * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hN _)).ne'
  rw [dimensionRatio_factorization r k row N hr hN, mul_div_cancel_left₀ _ hden]
  have hprod := Finset.norm_prod_one_add_sub_one_le Finset.univ (fun a => f a - 1)
  have hsum : (∑ a, |f a - 1|) ≤
      (r * k : ℕ) * ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N) := by
    calc
      _ ≤ ∑ _a : Fin r × Fin k,
          ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N) := by
        exact Finset.sum_le_sum (fun a _ => rescaled_factor_error r k row N δ hr hN hclose a)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hp : |(∏ a, f a) - 1| ≤ Real.exp (∑ a, |f a - 1|) - 1 := by
    have h1 (a) : 1 + (f a - 1) = f a := by ring
    simpa only [h1, Real.norm_eq_abs] using hprod
  exact hp.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)
