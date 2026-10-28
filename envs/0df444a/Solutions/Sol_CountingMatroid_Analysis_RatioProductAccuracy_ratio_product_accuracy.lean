-- Prove2me | solution 1 for CountingMatroid.Analysis.RatioProductAccuracy.ratio_product_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:03:26.361746+00:00
-- url     : https://prove2.me/submissions/0658822c-ca52-4f0e-806c-9d39a82e5c28

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_RatioProductAccuracy_ratio_error_power_bounds

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RatioProductAccuracy



/-- INTERNAL: Normalize each empirical ratio by the successive partition
sum ratio; all intermediate partition sums then cancel.
TEXLINE: main.tex:1290-1304 -/
theorem ratio_product_telescope (L : ℕ) (C R : ℕ → ℚ)
    (hC : ∀ j, 0 < C j) :
    C 0 * (∏ j ∈ Finset.range L, R j) =
      C L * ∏ j ∈ Finset.range L, R j / (C (j + 1) / C j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc, ih]
    field_simp [(hC L).ne', (hC (L + 1)).ne']



end CountingMatroid.Analysis.RatioProductAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · proved · rational Bernoulli bounds and exact telescoping establish the product interval from phasewise relative ratio bounds, replacing only the paper's logarithm calculation.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RatioProductAccuracy

/-- PAPER: main.tex:1290-1311
Phasewise relative ratio accuracy gives the final product interval. The
rational Bernoulli estimate above replaces the paper's logarithm bound. -/
theorem solution (L : ℕ) (ε : ℚ) (C R : ℕ → ℚ)
    (hε : 0 < ε) (hεone : ε < 1) (hC : ∀ j, 0 < C j)
    (hR : ∀ j < L,
      (1 - ε / (32 * ((L : ℚ) + 1))) / (1 + ε / (32 * ((L : ℚ) + 1))) ≤
        R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤
        (1 + ε / (32 * ((L : ℚ) + 1))) / (1 - ε / (32 * ((L : ℚ) + 1)))) :
    (1 - ε / 4) * C L ≤ C 0 * (∏ j ∈ Finset.range L, R j) ∧
      C 0 * (∏ j ∈ Finset.range L, R j) ≤ (1 + ε / 4) * C L := by
  let η := ε / (32 * ((L : ℚ) + 1))
  let a := (1 - η) / (1 + η)
  let b := (1 + η) / (1 - η)
  let errors := fun j => R j / (C (j + 1) / C j)
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηsmall : η < 1 := by
    dsimp [η]
    apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 32 * ((L : ℚ) + 1))).mpr
    have := Nat.cast_nonneg (α := ℚ) L
    linarith
  have ha : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have hl : a ^ L ≤ ∏ j ∈ Finset.range L, errors j := by
    simpa using Finset.prod_le_prod (s := Finset.range L)
      (f := fun _ => a) (g := errors) (fun _ _ => ha)
      (fun j hj => (hR j (Finset.mem_range.mp hj)).1)
  have hu : (∏ j ∈ Finset.range L, errors j) ≤ b ^ L := by
    simpa using Finset.prod_le_prod (s := Finset.range L)
      (f := errors) (g := fun _ => b)
      (fun j hj => ha.trans (hR j (Finset.mem_range.mp hj)).1)
      (fun j hj => (hR j (Finset.mem_range.mp hj)).2)
  have hp := ratio_error_power_bounds L ε hε hεone
  rw [ratio_product_telescope L C R hC]
  constructor
  · exact (mul_le_mul_of_nonneg_right (hp.1.trans hl) (hC L).le).trans_eq
      (mul_comm _ _)
  · exact (mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right (hu.trans hp.2) (hC L).le)
